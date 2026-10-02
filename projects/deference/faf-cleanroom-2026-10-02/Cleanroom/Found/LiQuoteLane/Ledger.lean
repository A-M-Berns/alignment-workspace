import Cleanroom.Found.LiQuoteLane.Defs
import Cleanroom.Found.LiAsympCalc.Luv
import LogicalInduction.Framework.Compactness

/-!
# `li-quote-lane` · Ledger: the ledger LUV is determined at the published value (T1.2, T1.5)

The semantic content of the ledger: which threshold is decided by which stage
(`ledgerSchedule_mem_iff`), functionality with no hypothesis (`ledgerSchedule_functional`),
the stage-form and theory-form determinacy of the ledger LUV at the published value
(`ledgerLuv_decided_by`, `ledgerLuv_determinedVia`), its `li-asymp-calc` corollaries, and the
re-exports of `bli-found`'s conservativity for the ledger process (`ledgerProcess_hworld`,
`ledgerProcess_conservative`).

**Why T1.5 matters for T1.2.** `LUV.DeterminedVia` quantifies over worlds consistent with every
stage; over an unsatisfiable stage it is vacuous, and FAF's
`isLogicalInductor_of_stage_unsatisfiable` would then make every market an inductor. Functionality
(no hypothesis) plus `extendBy_hworld` (base free of family 3, base satisfiable) is what rules
this out; every row that uses `ledgerLuv_determinedVia` cites `ledgerProcess_hworld`.

Scope: one-way throughout.
-/

namespace Cleanroom.Found.LiQuoteLane

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiAsympCalc
open Filter Topology

/-! ## Membership -/

/-- Membership in a stage of the ledger schedule, generic form.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_ledgerSchedule_iff {a : ℕ → ℕ → ℚ} {e : ℕ → PublicationSchedule} {s : ℕ}
    {x : ℕ × ℕ × Bool} :
    x ∈ (ledgerSchedule a e).lits s ↔ ∃ n j c, n ≤ s ∧ j ≤ s ∧ c ≤ s ∧ (e j).e n ≤ s ∧
      (Encodable.decode (α := ℚ) c).isSome = true ∧ x = ledgerEntry a j n c := by
  rw [ledgerSchedule_lits, List.mem_toFinset, mem_ledgerEntries]

/-- **Which threshold is decided by which stage** (disclosure (α)): the literal for item `j`,
day `n`, threshold `r` with polarity `b` is in stage `s` iff `n, j, ⌜r⌝ ≤ s`, the item has been
published (`(e j).e n ≤ s`), and `b` is FAF's strict polarity `decide (r < a j n)`. In
particular every threshold is decided by stage `max n j ⌜r⌝ ((e j).e n)`, and every rational
threshold is decided eventually (all that `DeterminedVia` and the limit headlines need).
**What the code bound does not give:** at stage `n` the ledger decides the thresholds whose
*codes* are `≤ n`, not the corpus's grid `k/n` — `Encodable.encode (k/n)` exceeds `n` for most
`k/n` — so a dependent wanting "`α_{j,n}` decided to precision `1/n` by stage `n`" (the source's
trader-level proof of L4 uses that) will not get it from this schedule as stated; the precision
available at stage `n` is that of the rationals with code `≤ n` (audit r1 fidelity N6).
Source: mandate T1.1 (α); [[setting-and-notation]] lines 50–71
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem ledgerSchedule_mem_iff (a : ℕ → ℕ → ℚ) (e : ℕ → PublicationSchedule) (j n : ℕ)
    (r : ℚ) (b : Bool) (s : ℕ) :
    (ledgerFamily, ledgerPayload j n (Encodable.encode r), b) ∈ (ledgerSchedule a e).lits s ↔
      n ≤ s ∧ j ≤ s ∧ Encodable.encode r ≤ s ∧ (e j).e n ≤ s ∧ b = decide (r < a j n) := by
  rw [mem_ledgerSchedule_iff]
  constructor
  · rintro ⟨n', j', c', hn, hj, hc, he, -, hx⟩
    simp only [ledgerEntry, Prod.mk.injEq] at hx
    obtain ⟨-, hp, hb⟩ := hx
    obtain ⟨rfl, rfl, rfl⟩ := ledgerPayload_inj.mp hp
    rw [ratOfCode_encode] at hb
    exact ⟨hn, hj, hc, he, hb⟩
  · rintro ⟨hn, hj, hc, he, rfl⟩
    exact ⟨n, j, Encodable.encode r, hn, hj, hc, he, by simp, by simp [ledgerEntry]⟩

/-- Every family the ledger schedule uses is the ledger family `3`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma ledgerSchedule_families (a : ℕ → ℕ → ℚ) (e : ℕ → PublicationSchedule) :
    ∀ f ∈ (ledgerSchedule a e).families, f = ledgerFamily := by
  rintro f ⟨s, x, hx, rfl⟩
  rw [mem_ledgerSchedule_iff] at hx
  obtain ⟨n, j, c, -, -, -, -, -, rfl⟩ := hx
  rfl

/-! ## T1.5: functionality, `hworld`, conservativity -/

/-- **The ledger schedule is functional, with no hypothesis**: the polarity of a triple is a
function of its payload `⟨n, ⟨j, c⟩⟩`, so no stage carries both an atom and its negation. This is
what keeps every stage of `ledgerProcess` satisfiable (with `ledgerProcess_hworld`) and so keeps
`isLogicalInductor_of_stage_unsatisfiable` out of every row that uses `ledgerLuv_determinedVia`.
Source: mandate T1.5; anson-012 (via `bli-found`)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem ledgerSchedule_functional (a : ℕ → ℕ → ℚ) (e : ℕ → PublicationSchedule) :
    (ledgerSchedule a e).Functional := by
  rintro s f p ⟨hpos, hneg⟩
  rw [mem_ledgerSchedule_iff] at hpos hneg
  obtain ⟨n, j, c, -, -, -, -, -, h1⟩ := hpos
  obtain ⟨n', j', c', -, -, -, -, -, h2⟩ := hneg
  simp only [ledgerEntry, Prod.mk.injEq] at h1 h2
  obtain ⟨-, hp1, hb1⟩ := h1
  obtain ⟨-, hp2, hb2⟩ := h2
  obtain ⟨rfl, rfl, rfl⟩ := ledgerPayload_inj.mp (hp1.symm.trans hp2)
  have h : true = false := hb1.trans hb2.symm
  simp at h

/-- A world consistent with every stage of a base process free of the ledger extends (by
overriding the ledger atoms only) to a world consistent with every stage of the ledger process.
Source: mandate T1.5 (anson-012 via `bli-found`'s `extendBy_consistentWithTheory`)
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem ledgerProcess_consistentWithTheory {base : DeductiveProcess} {a : ℕ → ℕ → ℚ}
    {e : ℕ → PublicationSchedule} (hfree : ProcessFreeOf (ledgerSchedule a e) base)
    {v : PCWorld} (hv : v.ConsistentWithTheory base) :
    (override (ledgerSchedule a e) v).ConsistentWithTheory (ledgerProcess base a e) :=
  extendBy_consistentWithTheory (ledgerSchedule_functional a e) hfree hv

/-- **`hworld` for the ledger process**: if every stage of the base has a consistent world and the
base is free of the ledger's atoms, every stage of `ledgerProcess base a e` has one. This is the
guard against `isLogicalInductor_of_stage_unsatisfiable`; cite it with every use of
`ledgerLuv_determinedVia`.
Source: mandate T1.5 (anson-012 via `bli-found`'s `extendBy_hworld`)
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem ledgerProcess_hworld {base : DeductiveProcess} {a : ℕ → ℕ → ℚ}
    {e : ℕ → PublicationSchedule} (hfree : ProcessFreeOf (ledgerSchedule a e) base)
    (h : ∀ n, ∃ v : PCWorld, v.ConsistentWith (base.D n)) :
    ∀ n, ∃ v : PCWorld, v.ConsistentWith ((ledgerProcess base a e).D n) :=
  extendBy_hworld (ledgerSchedule_functional a e) hfree h

/-- **The world quantifier of T1.2 is non-empty**: under T1.5's hypotheses there is one world
consistent with *every* stage of the ledger process (FAF's propositional compactness,
`DeductiveProcess.exists_consistentWithTheory`, on `ledgerProcess_hworld`). This is the bridge
from the per-stage `hworld` to the theory-level quantifier of `LUV.DeterminedVia`; cite it (or
`ledgerProcess_hworld` + this name) with every use of `ledgerLuv_determinedVia`.
Source: mandate T1.5 (non-vacuity of T1.2); audit r1 fidelity N8 / adversarial 2
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem ledgerProcess_theoryWorld {base : DeductiveProcess} {a : ℕ → ℕ → ℚ}
    {e : ℕ → PublicationSchedule} (hfree : ProcessFreeOf (ledgerSchedule a e) base)
    (h : ∀ n, ∃ v : PCWorld, v.ConsistentWith (base.D n)) :
    ∃ v : PCWorld, v.ConsistentWithTheory (ledgerProcess base a e) :=
  DeductiveProcess.exists_consistentWithTheory _ (ledgerProcess_hworld hfree h)

/-- A sentence tag-free for the ledger family is free of the ledger schedule.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma freeOf_ledgerSchedule_of_tagFree {a : ℕ → ℕ → ℚ} {e : ℕ → PublicationSchedule}
    {φ : Sentence} (hφ : TagFreeSentence (cleanroomBaseTag + ledgerFamily) φ) :
    FreeOf (ledgerSchedule a e) φ :=
  FreeOf.of_tagFree fun f hf => by rw [ledgerSchedule_families a e f hf]; exact hφ

/-- A process tag-free for the ledger family is free of the ledger schedule.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma processFreeOf_ledgerSchedule_of_tagFree {a : ℕ → ℕ → ℚ} {e : ℕ → PublicationSchedule}
    {DP : DeductiveProcess} (h : TagFreeProcess (cleanroomBaseTag + ledgerFamily) DP) :
    ProcessFreeOf (ledgerSchedule a e) DP :=
  fun k φ hφ => freeOf_ledgerSchedule_of_tagFree (h k φ hφ)

/-- A cleanroom-free process (every FAF-built process) is free of the ledger schedule.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma processFreeOf_ledgerSchedule_of_cleanroomFree {a : ℕ → ℕ → ℚ}
    {e : ℕ → PublicationSchedule} {DP : DeductiveProcess} (h : CleanroomFreeProcess DP) :
    ProcessFreeOf (ledgerSchedule a e) DP :=
  ProcessFreeOf.of_cleanroomFree h _

/-- **Conservativity, theory form**: the ledger process decides no new sentence of the base
language — for `φ` tag-free for family `3`, `φ` holds in every completed-theory world of the
ledger process iff it does in every completed-theory world of the base. "Decided" is FAF's
semantic reading (`∀ v, ConsistentWithTheory → Holds`), as in `bli-found`.
Source: mandate T1.5 (anson-012 via `bli-found`'s `extendBy_decidesTheory_iff`)
Kind: C
Fidelity: variant: semantic "decided" in place of anson-012's Γ-complete-process membership
Hyps: (a) none -/
theorem ledgerProcess_conservative {base : DeductiveProcess} {a : ℕ → ℕ → ℚ}
    {e : ℕ → PublicationSchedule} (hfree : ProcessFreeOf (ledgerSchedule a e) base)
    {φ : Sentence} (hφ : TagFreeSentence (cleanroomBaseTag + ledgerFamily) φ) :
    (∀ v : PCWorld, v.ConsistentWithTheory (ledgerProcess base a e) → v.Holds φ) ↔
      (∀ v : PCWorld, v.ConsistentWithTheory base → v.Holds φ) :=
  extendBy_decidesTheory_iff (ledgerSchedule_functional a e) hfree
    (freeOf_ledgerSchedule_of_tagFree hφ)

/-- **Conservativity, stage form**: at every stage `n`, a family-3-free sentence is decided by the
ledger process iff it is decided by the base.
Source: mandate T1.5 (anson-012 via `bli-found`'s `extendBy_decides_iff`)
Kind: C
Fidelity: variant: semantic "decided"
Hyps: (a) none -/
theorem ledgerProcess_decides_iff {base : DeductiveProcess} {a : ℕ → ℕ → ℚ}
    {e : ℕ → PublicationSchedule} (hfree : ProcessFreeOf (ledgerSchedule a e) base)
    {φ : Sentence} (hφ : TagFreeSentence (cleanroomBaseTag + ledgerFamily) φ) (n : ℕ) :
    (∀ v : PCWorld, v.ConsistentWith ((ledgerProcess base a e).D n) → v.Holds φ) ↔
      (∀ v : PCWorld, v.ConsistentWith (base.D n) → v.Holds φ) :=
  extendBy_decides_iff (ledgerSchedule_functional a e) hfree
    (freeOf_ledgerSchedule_of_tagFree hφ) n

/-! ## T1.2: the ledger LUV is determined at the published value -/

/-- **Stage form of determinacy.** Once stage `s` has passed `n`, `j`, `⌜r⌝` and the publication
stage `(e j).e n`, every world consistent with stage `s` of the ledger process affirms
`⌜α_{j,n} > r⌝` when `r < a j n` and denies it when `a j n ≤ r`.
Source: mandate T1.2 (stage form); [[setting-and-notation]] lines 50–71
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem ledgerLuv_decided_by (base : DeductiveProcess) (a : ℕ → ℕ → ℚ)
    (e : ℕ → PublicationSchedule) (j n : ℕ) (r : ℚ) {s : ℕ}
    (hs : n ≤ s ∧ j ≤ s ∧ Encodable.encode r ≤ s ∧ (e j).e n ≤ s) (v : PCWorld)
    (hv : v.ConsistentWith ((ledgerProcess base a e).D s)) :
    (r < a j n → v.Holds ((ledgerLuv j n).gt r)) ∧
      (a j n ≤ r → ¬ v.Holds ((ledgerLuv j n).gt r)) := by
  have hmem : ∀ b, b = decide (r < a j n) →
      (ledgerFamily, ledgerPayload j n (Encodable.encode r), b) ∈ (ledgerSchedule a e).lits s :=
    fun b hb => (ledgerSchedule_mem_iff a e j n r b s).mpr ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2, hb⟩
  have hlit : ∀ b, b = decide (r < a j n) →
      v.Holds (literalOf (ledgerFamily, ledgerPayload j n (Encodable.encode r), b)) := by
    intro b hb
    apply hv
    rw [ledgerProcess_D, Finset.mem_union]
    exact Or.inr (Finset.mem_image.mpr ⟨_, hmem b hb, rfl⟩)
  constructor
  · intro hr
    have := hlit true (decide_eq_true hr).symm
    simpa using this
  · intro hr
    have := hlit false (decide_eq_false (not_lt.mpr hr)).symm
    rw [literalOf_false, PCWorld.holds_neg] at this
    exact this

/-- **T1.2 (headline). The ledger LUV is determined at the published value**: for a table with
values in `[0,1]`, every world consistent with every stage of `ledgerProcess base a e` values
`α_{j,n}` at `a j n` (FAF's `PCWorld.ValuesAt`: thresholds below the value affirmed, above it
denied). The positive literal for `r < a j n` and the negative literal for `a j n < r` are in
stage `max n j ⌜r⌝ ((e j).e n)` (`ledgerLuv_decided_by`). `hmem` is needed, not vacuous: `ValuesAt`
demands `0 ≤ a j n ≤ 1`, and without it the theorem is false, not empty. **Non-vacuity of the
quantifier**: `DeterminedVia` ranges over worlds consistent with *every* stage; `ledgerProcess_hworld`
(T1.5) gives a world per stage, and FAF's propositional compactness
(`DeductiveProcess.exists_consistentWithTheory`) turns that into one world for the whole theory —
packaged as `ledgerProcess_theoryWorld` below. So when the base is free of family 3 and
satisfiable, this is a statement about a non-empty set of worlds. Scope: one-way.
Source: [[setting-and-notation]] lines 50–71 (vq-wiki-001); [[deference-in-logical-induction-v6]] §0.4 lines 100–104 ("a quote ledger of threshold atoms … that `D` decides to the published value"); root-deference-036; root-fa-001 (ii)
Kind: C
Fidelity: exact, with disclosures (α) code-bounded thresholds and (β) strict polarity (`Defs.lean`)
Hyps: (a) none (`hmem` is the `[0,1]` range of the published table, discharged for LIA quotes by `liaHistory_range` in `OneWay.lean`) -/
theorem ledgerLuv_determinedVia (base : DeductiveProcess) (a : ℕ → ℕ → ℚ)
    (e : ℕ → PublicationSchedule) (hmem : ∀ j n, 0 ≤ a j n ∧ a j n ≤ 1) (j n : ℕ) :
    LUV.DeterminedVia (ledgerLuv j n) (ledgerProcess base a e) (a j n) := by
  intro v hv
  unfold PCWorld.ValuesAt
  refine ⟨by exact_mod_cast (hmem j n).1, by exact_mod_cast (hmem j n).2, fun r => ?_⟩
  have hs : n ≤ max (max n j) (max (Encodable.encode r) ((e j).e n)) ∧
      j ≤ max (max n j) (max (Encodable.encode r) ((e j).e n)) ∧
      Encodable.encode r ≤ max (max n j) (max (Encodable.encode r) ((e j).e n)) ∧
      (e j).e n ≤ max (max n j) (max (Encodable.encode r) ((e j).e n)) :=
    ⟨le_max_of_le_left (le_max_left _ _), le_max_of_le_left (le_max_right _ _),
      le_max_of_le_right (le_max_left _ _), le_max_of_le_right (le_max_right _ _)⟩
  have h := ledgerLuv_decided_by base a e j n r hs v (hv _)
  constructor
  · intro hr
    exact h.1 (by exact_mod_cast hr)
  · intro hr
    exact h.2 (by exact_mod_cast hr.le)

/-- **T1.2, `LUVCombination.DeterminedViaTheory` form** (the plan's target (2), discharged for the
ledger LUV): the singleton combinations `0 + 1·α_{j,n}` are determined via the ledger process at
the published values, for any market `P`.
Source: mandate T1.2 (corollary via `li-asymp-calc`'s `DeterminedVia.determinedViaTheory_ofLUV`)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem ledgerLuv_determinedViaTheory (P : History) (base : DeductiveProcess) (a : ℕ → ℕ → ℚ)
    (e : ℕ → PublicationSchedule) (hmem : ∀ j n, 0 ≤ a j n ∧ a j n ≤ 1) (j : ℕ) :
    LUVCombination.DeterminedViaTheory (fun n => LUVCombination.ofLUV (ledgerLuv j n)) P
      (ledgerProcess base a e) (fun n => (a j n : ℝ)) :=
  DeterminedVia.determinedViaTheory_ofLUV P (fun n => ledgerLuv_determinedVia base a e hmem j n)

/-- **T1.2, world-valued form**: every completed-theory world values every ledger LUV.
Source: mandate T1.2 (corollary via `li-asymp-calc`)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem ledgerLuv_worldValued (base : DeductiveProcess) (a : ℕ → ℕ → ℚ)
    (e : ℕ → PublicationSchedule) (hmem : ∀ j n, 0 ≤ a j n ∧ a j n ≤ 1) (j : ℕ) :
    LUVCombination.WorldValued (fun n => LUVCombination.ofLUV (ledgerLuv j n))
      (ledgerProcess base a e) :=
  DeterminedVia.worldValued_ofLUV (fun n => ledgerLuv_determinedVia base a e hmem j n)

/-- **T1.2, mesh form**: the precision-`(n+1)` threshold mesh of `α_{j,n}` is approximately
determined via the ledger process at `a j n` with error `1/(n+1)` (FAF's
`AffineCombination.ApproxDeterminedViaTheory`), the input of `lic_wubaff` /
`affine_provind_theory_*`.
Source: mandate T1.2 (corollary via `li-asymp-calc`'s `DeterminedVia.approxDetermined_mesh_ofLUV`)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem ledgerLuv_approxDetermined_mesh (P : History) (base : DeductiveProcess)
    (a : ℕ → ℕ → ℚ) (e : ℕ → PublicationSchedule) (hmem : ∀ j n, 0 ≤ a j n ∧ a j n ≤ 1)
    (j : ℕ) :
    AffineCombination.ApproxDeterminedViaTheory
      (fun n => (LUVCombination.ofLUV (ledgerLuv j n)).meshAffine (n + 1)) P
      (ledgerProcess base a e) (fun n => (a j n : ℝ)) (fun n => 1 / ((n : ℝ) + 1)) :=
  DeterminedVia.approxDetermined_mesh_ofLUV P
    (fun n => ledgerLuv_determinedVia base a e hmem j n)

/-! ## Non-degeneracy of the schedule (for the N+ rows) -/

/-- The ledger is not a constant schedule: for a `[0,1]`-valued table, the threshold `-1` is
affirmed and the threshold `2` is denied, for every item and day, at some stage. Both polarities
occur.
Source: mandate T6.2 (what "day-varying quotes" can mean here)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem ledgerSchedule_both_polarities (a : ℕ → ℕ → ℚ) (e : ℕ → PublicationSchedule)
    (hmem : ∀ j n, 0 ≤ a j n ∧ a j n ≤ 1) (j n : ℕ) :
    (∃ s, (ledgerFamily, ledgerPayload j n (Encodable.encode (-1 : ℚ)), true) ∈
        (ledgerSchedule a e).lits s) ∧
      ∃ s, (ledgerFamily, ledgerPayload j n (Encodable.encode (2 : ℚ)), false) ∈
        (ledgerSchedule a e).lits s := by
  constructor
  · refine ⟨max (max n j) (max (Encodable.encode (-1 : ℚ)) ((e j).e n)), ?_⟩
    rw [ledgerSchedule_mem_iff]
    refine ⟨le_max_of_le_left (le_max_left _ _), le_max_of_le_left (le_max_right _ _),
      le_max_of_le_right (le_max_left _ _), le_max_of_le_right (le_max_right _ _), ?_⟩
    have : (-1 : ℚ) < a j n := by linarith [(hmem j n).1]
    simp [this]
  · refine ⟨max (max n j) (max (Encodable.encode (2 : ℚ)) ((e j).e n)), ?_⟩
    rw [ledgerSchedule_mem_iff]
    refine ⟨le_max_of_le_left (le_max_left _ _), le_max_of_le_left (le_max_right _ _),
      le_max_of_le_right (le_max_left _ _), le_max_of_le_right (le_max_right _ _), ?_⟩
    have : ¬ ((2 : ℚ) < a j n) := by linarith [(hmem j n).2]
    simp [this]

/-- The ledger atoms of different items or days are different atoms (the schedule varies with the
day and with the item).
Source: mandate T6.2
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem ledgerLuv_gt_ne {j n j' n' : ℕ} (h : n ≠ n' ∨ j ≠ j') (r r' : ℚ) :
    (ledgerLuv j n).gt r ≠ (ledgerLuv j' n').gt r' := by
  intro heq
  simp only [ledgerLuv_gt] at heq
  have := (freshAtom_inj.mp heq).2
  rw [ledgerPayload_inj] at this
  rcases h with h | h
  · exact h this.1
  · exact h this.2.1

end Cleanroom.Found.LiQuoteLane
