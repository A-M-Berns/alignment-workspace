import Cleanroom.Deference.DefObstruction.Carrier
import LogicalInduction.Properties.NonDogmatism
import LogicalInduction.Properties.AffinePersistence

/-!
# `def-obstruction` · Fragment: the non-dogmatism cluster over the ledger process (T7)

The decided fragment trusts cleanly, the undecided fragment is confined to `(0,1)`, the two
fragments are exactly where the limiting belief is `{0,1}`-valued or not, and no market is a
logical inductor over both a process and its atom extension (the two-sided "not monotone in
either direction", an inductor on each side, is `FragmentWitness.lean`'s
`criterion_not_monotone_either_direction`). All (a): FAF's `lic_provind_true` /
`lic_provind_false` (constant families), `lic_exists_limit_pos` / `lic_exists_limit_lt_one`
(`thm:nd`), `lic_limitingBelief_tendsto` (`thm:con`), and `li-quote-lane`'s conservativity of the
ledger extension (`ledgerProcess_decides_iff`, `extendBy_consistentWith`).

**"Decided" is semantic** (`DecidedTrueAt`: some stage all of whose consistent worlds affirm `φ`),
as in `bli-found`/`li-quote-lane`; stage membership `φ ∈ DP.D k` is the special case
(`DecidedTrueAt.of_mem`). **"Undecided" is semantic too** (`Undecided`: at every stage both
polarities have a consistent world) — the hypothesis `thm:nd` takes, and the one the ledger
extension preserves for tag-free sentences (`undecided_ledger`).

**No hypothesis on the table** anywhere in this file: the advised reader `H` is any inductor over
`ledgerProcess DPH a e` for any table `a`. This is the fail-safety sentence of
[[self-referential-settlement-target]] §5.4: on the decided fragment deference buys speed, never
truth, whatever `A` publishes.

**T7(d), the refuted construction and the structural extension** (`adjoinAtom`,
`not_inductor_base_of_inductor_adjoin`, `not_inductor_adjoin_of_inductor_base`,
`criterion_not_monotone_in_process`): the process `E := DP ⊕ {φ}` that decides a fresh atom `φ`
at every stage has inductors whose price of `φ` tends to `1`, so none of them is an inductor over
`DP` (where `thm:nd` keeps the limit below `1`); and no inductor over `DP` is one over `E`. The
N+ instances over FAF's LIA are in `FragmentWitness.lean`.

Scope: one-way throughout (the reader's process; `A` is nowhere).
-/

namespace Cleanroom.Deference.DefObstruction

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiQuoteLane
open Cleanroom.Found.LiAsympCalc Cleanroom.Li.LiDiagonal
open Filter Topology

/-! ## A. Decided and undecided, semantically -/

/-- **Decided true at some stage** (semantic): every world consistent with stage `k` of `DP`
affirms `φ`. Stage membership implies it (`DecidedTrueAt.of_mem`); FAF's completed-theory
"theorem" is implied by it.
Scope: one process.
Source: [[self-referential-settlement-target]] §5.4 ("`Γ`-decided"); `bli-found`/`li-quote-lane`'s semantic "decided" (anson-012)
Kind: D
Fidelity: variant: semantic "decided" in place of `Γ ⊢ φ` (stage membership is the special case)
Hyps: n/a -/
def DecidedTrueAt (DP : DeductiveProcess) (φ : Sentence) : Prop :=
  ∃ k, ∀ v : PCWorld, v.ConsistentWith (DP.D k) → v.Holds φ

/-- **Decided false at some stage** (semantic).
Scope: one process.
Source: as `DecidedTrueAt`
Kind: D
Fidelity: variant: semantic
Hyps: n/a -/
def DecidedFalseAt (DP : DeductiveProcess) (φ : Sentence) : Prop :=
  ∃ k, ∀ v : PCWorld, v.ConsistentWith (DP.D k) → ¬ v.Holds φ

/-- **Decided** (either way) at some stage.
Scope: one process.
Source: as `DecidedTrueAt`
Kind: D
Fidelity: variant: semantic
Hyps: n/a -/
def Decided (DP : DeductiveProcess) (φ : Sentence) : Prop :=
  DecidedTrueAt DP φ ∨ DecidedFalseAt DP φ

/-- **Undecided** (semantic): at every stage both `φ` and `∼φ` have a consistent world. This is
the hypothesis FAF's `thm:nd` (`lic_exists_limit_pos`, `lic_exists_limit_lt_one`) takes.
Scope: one process.
Source: [[self-referential-settlement-target]] §5.3 ("`Γ`-independent `φ`"); FAF `thm:nd`
Kind: D
Fidelity: variant: semantic independence at every stage
Hyps: n/a -/
def Undecided (DP : DeductiveProcess) (φ : Sentence) : Prop :=
  (∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n) ∧ v.Holds φ) ∧
    (∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n) ∧ ¬ v.Holds φ)

/-- Stage membership decides true.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem DecidedTrueAt.of_mem {DP : DeductiveProcess} {φ : Sentence} (h : ∃ k, φ ∈ DP.D k) :
    DecidedTrueAt DP φ := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, fun v hv => hv φ hk⟩

/-- Membership of the negation decides false.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem DecidedFalseAt.of_neg_mem {DP : DeductiveProcess} {φ : Sentence}
    (h : ∃ k, (∼ φ) ∈ DP.D k) : DecidedFalseAt DP φ := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, fun v hv => (PCWorld.holds_neg v φ).mp (hv _ hk)⟩

/-- Decided true at a stage implies true in every completed world.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem DecidedTrueAt.theory {DP : DeductiveProcess} {φ : Sentence} (h : DecidedTrueAt DP φ)
    (v : PCWorld) (hv : v.ConsistentWithTheory DP) : v.Holds φ := by
  obtain ⟨k, hk⟩ := h
  exact hk v (hv k)

/-- Decided false at a stage implies false in every completed world.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem DecidedFalseAt.theory {DP : DeductiveProcess} {φ : Sentence} (h : DecidedFalseAt DP φ)
    (v : PCWorld) (hv : v.ConsistentWithTheory DP) : ¬ v.Holds φ := by
  obtain ⟨k, hk⟩ := h
  exact hk v (hv k)

/-- An undecided sentence lives over a process with satisfiable stages.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Undecided.hworld {DP : DeductiveProcess} {φ : Sentence} (h : Undecided DP φ) :
    ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n) :=
  fun n => (h.1 n).imp fun _ hv => hv.1

/-! ## B. The limiting belief on decided sentences -/

/-- **Prices of a sentence decided true converge to `1`** under any inductor (FAF's
`lic_provind_true` on the constant family).
Scope: one process.
Source: [[self-referential-settlement-target]] §5.4 ((LI-PI) on decidables); LI `thm:provind`
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem price_tendsto_one_of_decidedTrue (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (φ : Sentence) (h : DecidedTrueAt DP φ) : Tendsto (fun n => P n φ) atTop (𝓝 1) := by
  have h1 := lic_provind_true P DP (fun _ => φ) (MachineSentenceCodes.const φ)
    (fun _ v hv => h.theory v hv) hworld
  exact convergesTo_iff_asympEq_const.mpr h1

/-- **Prices of a sentence decided false converge to `0`** (FAF's `lic_provind_false`).
Scope: one process.
Source: [[self-referential-settlement-target]] §5.4; LI `thm:provind`
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem price_tendsto_zero_of_decidedFalse (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (φ : Sentence) (h : DecidedFalseAt DP φ) : Tendsto (fun n => P n φ) atTop (𝓝 0) := by
  have h1 := lic_provind_false P DP (fun _ => φ) (MachineSentenceCodes.const φ)
    (fun _ v hv => (PCWorld.holds_neg v φ).mpr (h.theory v hv)) hworld
  exact convergesTo_iff_asympEq_const.mpr h1

/-- The limiting belief is the limit, whenever the price sequence converges (FAF's `thm:con`
plus uniqueness of limits).
Source: none: infrastructure (FAF `lic_limitingBelief_tendsto`)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem limitingBelief_eq_of_tendsto (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (φ : Sentence) {L : ℝ} (h : Tendsto (fun n => P n φ) atTop (𝓝 L)) :
    limitingBelief P φ = L :=
  tendsto_nhds_unique (lic_limitingBelief_tendsto P DP hworld φ) h

/-- The limiting belief of a sentence decided true is `1`.
Source: [[self-referential-settlement-target]] §5.4
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem limitingBelief_eq_one_of_decidedTrue (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (φ : Sentence) (h : DecidedTrueAt DP φ) : limitingBelief P φ = 1 :=
  limitingBelief_eq_of_tendsto P DP hworld φ (price_tendsto_one_of_decidedTrue P DP hworld φ h)

/-- The limiting belief of a sentence decided false is `0`.
Source: [[self-referential-settlement-target]] §5.4
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem limitingBelief_eq_zero_of_decidedFalse (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (φ : Sentence) (h : DecidedFalseAt DP φ) : limitingBelief P φ = 0 :=
  limitingBelief_eq_of_tendsto P DP hworld φ (price_tendsto_zero_of_decidedFalse P DP hworld φ h)

/-! ## C. Transfer across the ledger extension -/

/-- **Decided-true transfers to the ledger process** (conservativity, stage form, one direction):
for a tag-free sentence decided true at stage `k` of the base, the same stage of the ledger
process decides it true, for every table.
Scope: one-way.
Source: `li-quote-lane` `ledgerProcess_decides_iff` (anson-012)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem DecidedTrueAt.ledger {DPH : DeductiveProcess} {a : ℕ → ℕ → ℚ}
    {e : ℕ → PublicationSchedule} (hfree : ProcessFreeOf (ledgerSchedule a e) DPH)
    {φ : Sentence} (hφ : TagFreeSentence (cleanroomBaseTag + ledgerFamily) φ)
    (h : DecidedTrueAt DPH φ) : DecidedTrueAt (ledgerProcess DPH a e) φ := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, (ledgerProcess_decides_iff hfree hφ k).mpr hk⟩

/-- **Decided-false transfers to the ledger process.**
Scope: one-way.
Source: `li-quote-lane` `ledgerProcess_decides_iff` (anson-012)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem DecidedFalseAt.ledger {DPH : DeductiveProcess} {a : ℕ → ℕ → ℚ}
    {e : ℕ → PublicationSchedule} (hfree : ProcessFreeOf (ledgerSchedule a e) DPH)
    {φ : Sentence} (hφ : TagFreeSentence (cleanroomBaseTag + ledgerFamily) φ)
    (h : DecidedFalseAt DPH φ) : DecidedFalseAt (ledgerProcess DPH a e) φ := by
  obtain ⟨k, hk⟩ := h
  have hk' : ∀ v : PCWorld, v.ConsistentWith (DPH.D k) → v.Holds (∼ φ) :=
    fun v hv => (PCWorld.holds_neg v φ).mpr (hk v hv)
  exact ⟨k, fun v hv => (PCWorld.holds_neg v φ).mp
    ((ledgerProcess_decides_iff hfree hφ.neg k).mpr hk' v hv)⟩

/-- **Decided-true transfers back from the ledger process to the base** (the other direction).
Scope: one-way.
Source: `li-quote-lane` `ledgerProcess_decides_iff` (anson-012)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem DecidedTrueAt.of_ledger {DPH : DeductiveProcess} {a : ℕ → ℕ → ℚ}
    {e : ℕ → PublicationSchedule} (hfree : ProcessFreeOf (ledgerSchedule a e) DPH)
    {φ : Sentence} (hφ : TagFreeSentence (cleanroomBaseTag + ledgerFamily) φ)
    (h : DecidedTrueAt (ledgerProcess DPH a e) φ) : DecidedTrueAt DPH φ := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, (ledgerProcess_decides_iff hfree hφ k).mp hk⟩

/-- **Decided-false transfers back from the ledger process to the base.**
Scope: one-way.
Source: `li-quote-lane` `ledgerProcess_decides_iff` (anson-012)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem DecidedFalseAt.of_ledger {DPH : DeductiveProcess} {a : ℕ → ℕ → ℚ}
    {e : ℕ → PublicationSchedule} (hfree : ProcessFreeOf (ledgerSchedule a e) DPH)
    {φ : Sentence} (hφ : TagFreeSentence (cleanroomBaseTag + ledgerFamily) φ)
    (h : DecidedFalseAt (ledgerProcess DPH a e) φ) : DecidedFalseAt DPH φ := by
  obtain ⟨k, hk⟩ := h
  have hk' : ∀ v : PCWorld, v.ConsistentWith ((ledgerProcess DPH a e).D k) → v.Holds (∼ φ) :=
    fun v hv => (PCWorld.holds_neg v φ).mpr (hk v hv)
  exact ⟨k, fun v hv => (PCWorld.holds_neg v φ).mp
    ((ledgerProcess_decides_iff hfree hφ.neg k).mp hk' v hv)⟩

/-- **Undecidedness transfers to the ledger process** (conservativity (i): a world consistent
with a stage of the base extends, by overriding the ledger atoms only, to one consistent with
the same stage of the ledger process, and the override does not touch a tag-free sentence).
Scope: one-way.
Source: `bli-found` `extendBy_consistentWith`, `override_holds_iff` (anson-012); [[self-referential-settlement-target]] §5.3 ("`D⁺_H` is conservative over `𝓛`")
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem Undecided.ledger {DPH : DeductiveProcess} {a : ℕ → ℕ → ℚ}
    {e : ℕ → PublicationSchedule} (hfree : ProcessFreeOf (ledgerSchedule a e) DPH)
    {φ : Sentence} (hφ : TagFreeSentence (cleanroomBaseTag + ledgerFamily) φ)
    (h : Undecided DPH φ) : Undecided (ledgerProcess DPH a e) φ := by
  have hL := ledgerSchedule_functional a e
  have hfφ : FreeOf (ledgerSchedule a e) φ := freeOf_ledgerSchedule_of_tagFree hφ
  constructor
  · intro n
    obtain ⟨v, hv, hφv⟩ := h.1 n
    refine ⟨override (ledgerSchedule a e) v, (extendBy_consistentWith hL hfree hv).1, ?_⟩
    exact (override_holds_iff (ledgerSchedule a e) v hfφ).mpr hφv
  · intro n
    obtain ⟨v, hv, hφv⟩ := h.2 n
    refine ⟨override (ledgerSchedule a e) v, (extendBy_consistentWith hL hfree hv).1, ?_⟩
    exact fun h' => hφv ((override_holds_iff (ledgerSchedule a e) v hfφ).mp h')

/-! ## D. T7(a): the decided fragment trusts cleanly -/

/-- **T7(a) (headline 5, decided half). The decided fragment trusts cleanly**: for a tag-free `φ`
decided true at some stage of the base `DPH`, both the autonomous reader `H₀` (an inductor over
`DPH`) and the advised reader `H` (the pair's inductor over `ledgerProcess DPH a e`) have limiting
belief `1` in `φ`; decided false, both have `0`. **No hypothesis on the table**: `A` may publish
anything. Testimony changes the trajectory, never the destination, on the decided fragment.
(`hfree` mentions `T.a` only nominally: the ledger schedule's *atom set* is table-independent —
`ledgerEntries` enumerates every `(n, j, ⌜r⌝)` and only the polarity depends on the table — so
freeness of the base from the ledger atoms is a property of `DPH` alone; the base's satisfiable
stages come from the carrier, `TablePair.hworld_base`. Audit r2 N3.)
Scope: one-way.
Source: [[self-referential-settlement-target]] §5.4 (anson-010); root-deference-030; [[deference-in-logical-induction-v6]] §4.5 ("the decided fragment trusts cleanly")
Kind: C
Fidelity: variant: semantic "decided" (stage form; membership is the special case `DecidedTrueAt.of_mem`)
Hyps: (a) none -/
theorem decided_fragment_trusts (T : TablePair) (H₀ : History) [IsLogicalInductor H₀ T.DPH]
    (hfree : ProcessFreeOf (ledgerSchedule T.a T.e) T.DPH)
    (φ : Sentence) (hφ : TagFreeSentence (cleanroomBaseTag + ledgerFamily) φ) :
    (DecidedTrueAt T.DPH φ → limitingBelief H₀ φ = 1 ∧ limitingBelief T.H φ = 1) ∧
    (DecidedFalseAt T.DPH φ → limitingBelief H₀ φ = 0 ∧ limitingBelief T.H φ = 0) := by
  haveI := T.H_inductor
  constructor
  · intro h
    exact ⟨limitingBelief_eq_one_of_decidedTrue H₀ T.DPH T.hworld_base φ h,
      limitingBelief_eq_one_of_decidedTrue T.H T.process T.hworld φ (h.ledger hfree hφ)⟩
  · intro h
    exact ⟨limitingBelief_eq_zero_of_decidedFalse H₀ T.DPH T.hworld_base φ h,
      limitingBelief_eq_zero_of_decidedFalse T.H T.process T.hworld φ (h.ledger hfree hφ)⟩

/-- **T7(a), stage-membership form**: `φ ∈ DPH.D k` for some `k` gives both limits `1`;
`∼φ ∈ DPH.D k` gives both `0`.
Scope: one-way.
Source: [[self-referential-settlement-target]] §5.4 (anson-010: "`𝟙[Γ ⊢ φ]`")
Kind: L (instance of `decided_fragment_trusts`)
Fidelity: exact (stage membership for `Γ ⊢ φ`)
Hyps: (a) none -/
theorem decided_fragment_trusts_of_mem (T : TablePair) (H₀ : History)
    [IsLogicalInductor H₀ T.DPH]
    (hfree : ProcessFreeOf (ledgerSchedule T.a T.e) T.DPH)
    (φ : Sentence) (hφ : TagFreeSentence (cleanroomBaseTag + ledgerFamily) φ) :
    ((∃ k, φ ∈ T.DPH.D k) → limitingBelief H₀ φ = 1 ∧ limitingBelief T.H φ = 1) ∧
    ((∃ k, (∼ φ) ∈ T.DPH.D k) → limitingBelief H₀ φ = 0 ∧ limitingBelief T.H φ = 0) :=
  ⟨fun h => (decided_fragment_trusts T H₀ hfree φ hφ).1 (DecidedTrueAt.of_mem h),
    fun h => (decided_fragment_trusts T H₀ hfree φ hφ).2 (DecidedFalseAt.of_neg_mem h)⟩

/-! ## E. T7(b): the undecided fragment is confined to the open interval -/

/-- **Non-dogmatism in limiting-belief form**: for an undecided `φ`, `0 < P∞(φ) < 1` under any
inductor (FAF's `thm:nd`, both directions, through `thm:con`).
Scope: one process.
Source: [[self-referential-settlement-target]] §5.3 (anson-008); LI `thm:nd`
Kind: C
Fidelity: exact (the open interval; the uniform margin `[δ_φ, 1 − δ_φ]` is not stated)
Hyps: (a) none -/
theorem limitingBelief_mem_Ioo (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (φ : Sentence) (h : Undecided DP φ) :
    0 < limitingBelief P φ ∧ limitingBelief P φ < 1 := by
  obtain ⟨L, hL, hpos⟩ := lic_exists_limit_pos P DP φ h.1
  obtain ⟨L', hL', hlt⟩ := lic_exists_limit_lt_one P DP φ h.2
  have e1 := limitingBelief_eq_of_tendsto P DP h.hworld φ hL
  have e2 := limitingBelief_eq_of_tendsto P DP h.hworld φ hL'
  exact ⟨e1 ▸ hpos, e2 ▸ hlt⟩

/-- **T7(b) (headline 5, undecided half). The undecided fragment is confined**: for a tag-free
`φ` undecided in the base, both the autonomous and the advised reader have limiting belief in
`(0,1)`. Whatever `A` publishes, it cannot drive certainty on an undecided proposition. (The
uniform margin `[δ_φ, 1 − δ_φ]` of the source is not stated: FAF's `lic_uniform_nonDogmatism`
needs an enumeration certificate this package does not build; stretch S4.)
Scope: one-way.
Source: [[self-referential-settlement-target]] §5.3 (anson-008); root-deference-029; lean-deference-017 (`manipulation_confined`, now with the margin derived rather than assumed)
Kind: C
Fidelity: weaker: the open interval `(0,1)`, not the uniform closed margin
Hyps: (a) none -/
theorem undecided_fragment_confined (T : TablePair) (H₀ : History) [IsLogicalInductor H₀ T.DPH]
    (hfree : ProcessFreeOf (ledgerSchedule T.a T.e) T.DPH)
    (φ : Sentence) (hφ : TagFreeSentence (cleanroomBaseTag + ledgerFamily) φ)
    (h : Undecided T.DPH φ) :
    (0 < limitingBelief H₀ φ ∧ limitingBelief H₀ φ < 1) ∧
    (0 < limitingBelief T.H φ ∧ limitingBelief T.H φ < 1) := by
  haveI := T.H_inductor
  exact ⟨limitingBelief_mem_Ioo H₀ T.DPH φ h,
    limitingBelief_mem_Ioo T.H T.process φ (h.ledger hfree hφ)⟩

/-! ## F. T7(c): the limiting belief is `{0,1}`-valued exactly on the decided fragment -/

/-- A limiting belief of `1` means some stage decides the sentence true (contrapositive of
`thm:nd`'s dual direction).
Source: anson-040 (the ⟹ direction); LI `thm:nd`
Kind: C
Fidelity: variant: semantic "decided"
Hyps: (a) none -/
theorem decidedTrue_of_limitingBelief_eq_one (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (φ : Sentence) (h : limitingBelief P φ = 1) : DecidedTrueAt DP φ := by
  have hnot : ¬ ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n) ∧ ¬ v.Holds φ := by
    intro hall
    obtain ⟨L, hL, hlt⟩ := lic_exists_limit_lt_one P DP φ hall
    rw [limitingBelief_eq_of_tendsto P DP hworld φ hL] at h
    linarith
  obtain ⟨k, hk⟩ := not_forall.mp hnot
  refine ⟨k, fun v hv => ?_⟩
  by_contra hnv
  exact hk ⟨v, hv, hnv⟩

/-- A limiting belief of `0` means some stage decides the sentence false.
Source: anson-040; LI `thm:nd`
Kind: C
Fidelity: variant: semantic "decided"
Hyps: (a) none -/
theorem decidedFalse_of_limitingBelief_eq_zero (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (φ : Sentence) (h : limitingBelief P φ = 0) : DecidedFalseAt DP φ := by
  have hnot : ¬ ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n) ∧ v.Holds φ := by
    intro hall
    obtain ⟨L, hL, hpos⟩ := lic_exists_limit_pos P DP φ hall
    rw [limitingBelief_eq_of_tendsto P DP hworld φ hL] at h
    linarith
  obtain ⟨k, hk⟩ := not_forall.mp hnot
  refine ⟨k, fun v hv hφ => ?_⟩
  exact hk ⟨v, hv, hφ⟩

/-- **T7(c): the limiting belief is extreme iff the sentence is decided** (anson-040's iff), for
any inductor over any process with satisfiable stages: `P∞(φ) ∈ {0,1} ↔ Decided DP φ`.
Scope: one process.
Source: anson-040 (chat 06: "a forced limit shift requires `φ` decided in `D⁺_H`"); [[self-referential-settlement-target]] §5.4
Kind: C
Fidelity: variant: semantic "decided"
Hyps: (a) none -/
theorem limitingBelief_extreme_iff_decided (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (φ : Sentence) :
    (limitingBelief P φ = 0 ∨ limitingBelief P φ = 1) ↔ Decided DP φ := by
  constructor
  · rintro (h | h)
    · exact Or.inr (decidedFalse_of_limitingBelief_eq_zero P DP hworld φ h)
    · exact Or.inl (decidedTrue_of_limitingBelief_eq_one P DP hworld φ h)
  · rintro (h | h)
    · exact Or.inr (limitingBelief_eq_one_of_decidedTrue P DP hworld φ h)
    · exact Or.inl (limitingBelief_eq_zero_of_decidedFalse P DP hworld φ h)

/-- **T7(c) over the ledger process**: the advised reader's limiting belief in a tag-free `φ` is
extreme iff the *base* decides `φ` — the ledger adds no decided sentence of the base language,
so no table can force a limit shift on an undecided sentence.
Scope: one-way.
Source: anson-040 (the ⟸/⟹ pair); root-deference-030/031
Kind: C
Fidelity: variant: semantic "decided"
Hyps: (a) none -/
theorem limitingBelief_extreme_iff_decided_base (T : TablePair)
    (hfree : ProcessFreeOf (ledgerSchedule T.a T.e) T.DPH)
    (φ : Sentence) (hφ : TagFreeSentence (cleanroomBaseTag + ledgerFamily) φ) :
    (limitingBelief T.H φ = 0 ∨ limitingBelief T.H φ = 1) ↔ Decided T.DPH φ := by
  haveI := T.H_inductor
  rw [limitingBelief_extreme_iff_decided T.H T.process T.hworld φ]
  constructor
  · rintro (h | h)
    · exact Or.inl (h.of_ledger hfree hφ)
    · exact Or.inr (h.of_ledger hfree hφ)
  · rintro (h | h)
    · exact Or.inl (h.ledger hfree hφ)
    · exact Or.inr (h.ledger hfree hφ)

/-! ## G. T7(d): the criterion is not monotone in the deductive process -/

/-- **The refuted stronger-process construction, the core fact**: for `φ` undecided in `DP`,
every inductor over `DP` has limiting belief `< 1` in `φ`. So no object with `P∞(φ) = 1` is an
inductor over `DP` — the construction of [[self-referential-settlement-target]] §6 produces an
inductor over a *different* process.
Scope: one process.
Source: [[self-referential-settlement-target]] §6 (anson-009); root-deference-031; lean-deference `nondogmatism_refutes` (now with the bound derived)
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem limitingBelief_lt_one_of_undecided (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (φ : Sentence) (h : Undecided DP φ) :
    limitingBelief P φ < 1 :=
  (limitingBelief_mem_Ioo P DP φ h).2

/-- **The one-literal schedule**: the fresh atom `freshAtom f p` adjoined (positively if `b`,
negatively otherwise) at every stage.
Scope: one process.
Source: mandate T7(d) ("`extendBy` with a fresh-atom literal")
Kind: D
Fidelity: n/a
Hyps: n/a -/
def atomSchedule (f p : ℕ) (b : Bool) : LiteralSchedule :=
  LiteralSchedule.ofList (fun _ => [(f, p, b)]) (fun _ _ hx => hx)

/-- The one-literal schedule is functional.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem atomSchedule_functional (f p : ℕ) (b : Bool) : (atomSchedule f p b).Functional := by
  rintro s f' p' ⟨h1, h2⟩
  simp only [atomSchedule, LiteralSchedule.ofList_lits, List.mem_toFinset, List.mem_singleton,
    Prod.mk.injEq] at h1 h2
  rw [← h1.2.2] at h2
  exact absurd h2.2.2 (by decide)

/-- **The stronger process `E := DP ⊕ {φ}`**: the base with the fresh atom `freshAtom f p`
adjoined as a decided fact at every stage.
Scope: one process.
Source: [[self-referential-settlement-target]] §6 ("`E ⊋ D⁺_H` that eventually settles an undecided `φ`"); mandate T7(d)
Kind: D
Fidelity: exact (the atom is decided at stage `0`; the source's "eventually" is the special case)
Hyps: n/a -/
def adjoinAtom (DP : DeductiveProcess) (f p : ℕ) : DeductiveProcess :=
  extendBy DP (atomSchedule f p true)

/-- The adjoined atom lies in every stage of `E`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem adjoinAtom_mem (DP : DeductiveProcess) (f p n : ℕ) :
    freshAtom f p ∈ (adjoinAtom DP f p).D n := by
  unfold adjoinAtom
  rw [extendBy_D]
  apply Finset.mem_union_right
  rw [Finset.mem_image]
  refine ⟨(f, p, true), ?_, rfl⟩
  simp [atomSchedule]

/-- `E` has satisfiable stages when `DP` does and is free of the atom.
Source: none: infrastructure (`bli-found` `extendBy_hworld`)
Kind: L
Fidelity: n/a -/
theorem adjoinAtom_hworld {DP : DeductiveProcess} {f p : ℕ}
    (hfree : ProcessFreeOf (atomSchedule f p true) DP)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ∀ n, ∃ v : PCWorld, v.ConsistentWith ((adjoinAtom DP f p).D n) :=
  extendBy_hworld (atomSchedule_functional f p true) hfree hworld

/-- `E` is computable when `DP` is.
Source: none: infrastructure (`bli-found` `extendBy_ofList_computable`)
Kind: L
Fidelity: n/a -/
theorem adjoinAtom_computable {DP : DeductiveProcess} (hDP : ComputableDeductiveProcess DP)
    (f p : ℕ) : ComputableDeductiveProcess (adjoinAtom DP f p) :=
  extendBy_ofList_computable hDP _ _ (Primrec.const _)

/-- **A fresh atom is undecided in a process free of it** (with satisfiable stages): both
polarities are realized at every stage, by adjoining the literal of either sign and taking a
world of the extension (`extendBy_hworld`), which is consistent with the base stage and settles
the atom as adjoined.
Scope: one process.
Source: [[self-referential-settlement-target]] §6 ("`D⁺_H` never decides `φ`"); mandate T7(d)
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem freshAtom_undecided {DP : DeductiveProcess} {f p : ℕ}
    (hfreeT : ProcessFreeOf (atomSchedule f p true) DP)
    (hfreeF : ProcessFreeOf (atomSchedule f p false) DP)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    Undecided DP (freshAtom f p) := by
  constructor
  · intro n
    obtain ⟨v, hv⟩ := extendBy_hworld (atomSchedule_functional f p true) hfreeT hworld n
    rw [extendBy_D] at hv
    refine ⟨v, fun φ hφ => hv φ (Finset.mem_union_left _ hφ), ?_⟩
    have hmem : literalOf (f, p, true) ∈ ((atomSchedule f p true).lits n).image literalOf := by
      rw [Finset.mem_image]
      exact ⟨(f, p, true), by simp [atomSchedule], rfl⟩
    have := hv _ (Finset.mem_union_right _ hmem)
    simpa using this
  · intro n
    obtain ⟨v, hv⟩ := extendBy_hworld (atomSchedule_functional f p false) hfreeF hworld n
    rw [extendBy_D] at hv
    refine ⟨v, fun φ hφ => hv φ (Finset.mem_union_left _ hφ), ?_⟩
    have hmem : literalOf (f, p, false) ∈ ((atomSchedule f p false).lits n).image literalOf := by
      rw [Finset.mem_image]
      exact ⟨(f, p, false), by simp [atomSchedule], rfl⟩
    have := hv _ (Finset.mem_union_right _ hmem)
    rw [literalOf_false, PCWorld.holds_neg] at this
    exact this

/-- A cleanroom-free process is free of every one-literal schedule.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem processFreeOf_atomSchedule_of_cleanroomFree {DP : DeductiveProcess}
    (h : CleanroomFreeProcess DP) (f p : ℕ) (b : Bool) : ProcessFreeOf (atomSchedule f p b) DP :=
  ProcessFreeOf.of_cleanroomFree h _

/-- **(i) An inductor over the stronger process is not one over the base**: over `E` the atom's
price tends to `1` (it is a stage-`0` fact of `E`), while over `DP` it is undecided and `thm:nd`
keeps every inductor's limit below `1`.
Scope: one process pair `DP ⊆ E`.
Source: [[self-referential-settlement-target]] §6 (anson-009: "the construction's `H⁺` is provably not an inductor over `D⁺_H`")
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem not_inductor_base_of_inductor_adjoin {DP : DeductiveProcess} {f p : ℕ}
    (hfreeT : ProcessFreeOf (atomSchedule f p true) DP)
    (hfreeF : ProcessFreeOf (atomSchedule f p false) DP)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (P : History) (hE : IsLogicalInductor P (adjoinAtom DP f p)) :
    ¬ IsLogicalInductor P DP := by
  intro hDP
  have h1 : Tendsto (fun n => P n (freshAtom f p)) atTop (𝓝 1) :=
    @price_tendsto_one_of_decidedTrue P _ hE (adjoinAtom_hworld hfreeT hworld) _
      (DecidedTrueAt.of_mem ⟨0, adjoinAtom_mem DP f p 0⟩)
  obtain ⟨L, hL, hlt⟩ :=
    @lic_exists_limit_lt_one P DP hDP (freshAtom f p) (freshAtom_undecided hfreeT hfreeF hworld).2
  have := tendsto_nhds_unique h1 hL
  linarith

/-- **(ii) An inductor over the base is not one over the stronger process** — the contrapositive
of (i), restated for use with the hypotheses in the other order (over `DP` its limit on the atom
is below `1`, but over `E` provability induction would force it to `1`). Same proposition as (i):
no market is an inductor over both processes.
Scope: one process pair `DP ⊆ E`.
Source: [[self-referential-settlement-target]] §6 (the monotonicity reversal); anson-009's extension ("both non-implications")
Kind: L (contrapositive of `not_inductor_base_of_inductor_adjoin`)
Fidelity: exact
Hyps: (a) none -/
theorem not_inductor_adjoin_of_inductor_base {DP : DeductiveProcess} {f p : ℕ}
    (hfreeT : ProcessFreeOf (atomSchedule f p true) DP)
    (hfreeF : ProcessFreeOf (atomSchedule f p false) DP)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (P : History) (hDP : IsLogicalInductor P DP) :
    ¬ IsLogicalInductor P (adjoinAtom DP f p) := by
  intro hE
  exact not_inductor_base_of_inductor_adjoin hfreeT hfreeF hworld P hE hDP

/-- **T7(d) (headline 5, structural half). No market is a logical inductor over both a process
and its atom extension**: for a process `DP` with satisfiable stages free of the atom
`freshAtom f p`, and `E := DP ⊕ {freshAtom f p}`, no `P` is an inductor over `DP` and over `E`.
This is the source's refutation ("shrinking the plausible-world set preserves 'bounded below' but
not 'unbounded above'": the construction's `H⁺` is provably not an inductor over `D⁺_H`)
generalized from one construction to every market; it is **one** proposition — "no inductor over
`E` is one over `DP`" and "no inductor over `DP` is one over `E`" are contrapositives of each
other, not two directions (repair round 1, audit B3). The genuinely two-sided statement — *non-
monotonicity in either direction*, an inductor on each side — needs an inductor over each process
and is `criterion_not_monotone_either_direction` (`FragmentWitness.lean`, over FAF's LIA).
Scope: one process pair.
Source: [[self-referential-settlement-target]] §6 (anson-009); root-deference-031
Kind: C
Fidelity: exact (the source's refutation, for every inductor)
Hyps: (a) none -/
theorem criterion_not_monotone_in_process {DP : DeductiveProcess} {f p : ℕ}
    (hfreeT : ProcessFreeOf (atomSchedule f p true) DP)
    (hfreeF : ProcessFreeOf (atomSchedule f p false) DP)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ∀ P : History, ¬ (IsLogicalInductor P DP ∧ IsLogicalInductor P (adjoinAtom DP f p)) :=
  fun P h => not_inductor_base_of_inductor_adjoin hfreeT hfreeF hworld P h.2 h.1

/-! ## H. T7(e): confinement (the trivial bound) -/

/-- **The limiting belief lies in `[0,1]`** (prices do; the interval is closed).
Scope: one process.
Source: anson-2-017 (pull Th 3 / Pull 1, the trivial half)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem limitingBelief_mem_Icc (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (φ : Sentence) :
    0 ≤ limitingBelief P φ ∧ limitingBelief P φ ≤ 1 := by
  have h := lic_limitingBelief_tendsto P DP hworld φ
  have hcl : IsClosed (Set.Icc (0 : ℝ) 1) := isClosed_Icc
  have hmem : limitingBelief P φ ∈ Set.Icc (0 : ℝ) 1 :=
    hcl.mem_of_tendsto h (Eventually.of_forall fun n =>
      IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n φ)
  exact hmem

end Cleanroom.Deference.DefObstruction
