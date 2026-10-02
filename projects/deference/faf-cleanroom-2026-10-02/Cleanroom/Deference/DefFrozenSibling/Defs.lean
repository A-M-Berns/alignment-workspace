import Cleanroom.Li.LiCoupledPair.Defs
import Cleanroom.Deference.DefTrackingPin.Defs

/-!
# `def-frozen-sibling` · Defs: the carrier `FrozenSystem` and the timely fragment

Package `Cleanroom.Deference.DefFrozenSibling` ([[def-frozen-sibling-mandate]] D1–D4). The
frozen-deliberation (sealed-sibling) construction of [[frozen-deliberation-deference-v6]] §5–§6:
three kinds of inductor on one clock — the **predictor `A`** (reader of the contract ledger), the
**advised reasoner `Hplus`** (reader of `A`'s quotes and, after settlement, of the settled values),
and the **sealed siblings `sib n`** (one per index, hearing only the quotes of days `< n`) — with
the contract `C_n` settled at `σ n` to `Y n := sib n (F n) (contract n)`, the sibling's exact
day-`F n` price of the contract proposition `P^{(n)}`, and the published quote `a n := 𝔼^A_n(C_n)`,
`A`'s day-`n` **expectation of the contract LUV**.

**Why not `li-coupled-pair`'s `SealedSiblingSystem` as shipped** (mandate D1): (i) its `a_eq` pins
the ledger to `A`'s *price of a quoted sentence*, so what `Hplus` reads is `A n (P^{(n)})` and every
on-`G` theorem would follow from `A`'s own provability induction with the contract and the sibling
idle — the "beside the claim" failure of [[AUDIT]] §3.3; the corpus's `a_n := A_n(C_n)` is `A`'s
*expectation of the contract LUV*, which is this carrier's `a_eq`. (ii) Its `Y_eq` pins `Y` to
FAF's LIA on the frozen process, which blocks the off-`G` counter-model (T5, `OffG.lean`), where
every sibling is a finite-support perturbation of the LIA. (iii) `Hplus` has no channel for the
settled value `Y n`, which T2 needs. The three components the two carriers share — `siblingProcess`
(the frozen ledger `D ⊕ Q^{<N}`), `ledgerProcess`, `ledgerLuv`, `PublicationSchedule`,
`DeferralFunction` — are `li-coupled-pair`'s / `li-quote-lane`'s / FAF's and are **not redefined**.

**Carrier, not claim.** `FrozenSystem` bundles the processes, tables and the facts a theorem needs;
it asserts nothing. The content is in the theorems over it (`Engine.lean`, `Tracking.lean`, …),
in the one-way instances (`offGSystem` in `OffG.lean`; `onGSystem`, `antiSystem` in `OnG.lean`)
and in the OPEN row of record `frozenSystem_exists` (`OffG.lean` §F): a theorem whose hypotheses
use `A_inductor` with `Y` the sibling's verdict is
**two-way** (`partial` over an OPEN pair: `frozenSystem_exists` for the global rows T1/T2;
`timely_cofinite_const` — the `base0` pair with the diagonal property, whose last conjunct
supplies an infinite timely fragment, `timely_all_of_diagonal` §F — for the on-`G` rows, since at
`frozenSystem_exists`'s pin non-emptiness of `G` is not established; repair round 2); one whose
hypotheses are only `Hplus_inductor` over a ledger of a *given* table, or `A_inductor` over a
ledger settled to a given table, is **one-way**.

**The fragment `G` is defined from the processes** (D2): `DecidedBy S n` is *stage membership* of
`contract n` or its negation in `base.D (F n)` — syntactic, because FAF's `DeductiveProcess.D` has
no closure (a sentence provable from the stage but not in it is not "decided" here) — and
`Timely S ε n` adds the tolerance clause `|Y n − truthAt S n| ≤ ε n`. `G` is never a parameter
set. The on-`G` theorems are stated along e.c. sub-fragments `G' = {n | t n = 0}` with
`t : ℕ → ℕ` a `UnaryRuler` (D3, `AgreeAlong`), never for a free set.

Names, fixed (every docstring says the role, never relies on the letter): `A` the predictor,
`Hplus` the advised reasoner, `sib n` the sealed sibling of index `n`, `base` the shared world
process `D`, `DPA0` `A`'s base process (the corpus's `D_A ⊇ D`, kept separate: `shared`),
`contract n` is `P^{(n)}`, `truthAt S n` its decided value, `Y n` the target, `a n` the published
quote, `F` the horizon, `eq` the quote's publication, `eY` the settled value's publication into the
`H`-side, `σ` settlement into `A`'s process; `G` the timely fragment, `G'` an e.c. sub-fragment.
-/

namespace Cleanroom.Deference.DefFrozenSibling

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiAsympCalc
  Cleanroom.Found.LiQuoteLane Cleanroom.Li.LiCoupledPair
open Filter Topology

/-! ## A. The `H`-side ledger: two items, the quote and the settled value -/

/-- The two-item table of the `H`-side ledger: item `0` is the published quote `a n`, every item
`j ≥ 1` is the settled value `Y n` (consistent duplicates, as `li-coupled-pair`'s `A`-side ledger
records `Y n` under every item index; item `1` is the one of record). Scope: the table `Hplus` and
every sibling read.
Source: [[frozen-deliberation-deference-v6]] §3 (the quote ledger) and §5 (settlement becomes public); mandate D1 ("`h 0 n := a n`, `h 1 n := Y n`")
Kind: D
Fidelity: exact (items `≥ 2` are duplicates of item `1`, disclosed)
Hyps: n/a -/
def frozenTable (a Y : ℕ → ℚ) (j n : ℕ) : ℚ := if j = 0 then a n else Y n

/-- The per-item publication schedules of the `H`-side ledger: item `0` (the quote) on `eq`, every
other item (the settled value) on `eY`.
Source: mandate D1
Kind: D
Fidelity: exact
Hyps: n/a -/
def frozenSched (eq eY : PublicationSchedule) (j : ℕ) : PublicationSchedule :=
  if j = 0 then eq else eY

/-- `frozenTable_zero`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma frozenTable_zero (a Y : ℕ → ℚ) (n : ℕ) : frozenTable a Y 0 n = a n := rfl

/-- `frozenTable_succ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma frozenTable_succ (a Y : ℕ → ℚ) (j n : ℕ) : frozenTable a Y (j + 1) n = Y n := by
  simp [frozenTable]

/-- `frozenSched_zero`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma frozenSched_zero (eq eY : PublicationSchedule) : frozenSched eq eY 0 = eq := rfl

/-- `frozenSched_succ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma frozenSched_succ (eq eY : PublicationSchedule) (j : ℕ) :
    frozenSched eq eY (j + 1) = eY := by simp [frozenSched]

/-! ## B. D1: the carrier -/

/-- **The frozen-deliberation system** (D1, the two-way carrier of this package). Fields: the
shared world process `base` (`D`) and the predictor's base `DPA0` (`D_A ⊇ D`, `shared`); the
schedules — the quote is published into the `H`-side ledger at `eq` **before** the horizon `F`
(`eq_lt_F`), the contract settles into `A`'s process at `σ` **after** the horizon (`F_lt_σ`), and
the settled value reaches the `H`-side ledger at `eY` no earlier than settlement (`σ_le_eY`); the
contract family `contract n` (`P^{(n)}`, an e.c. family of sentences of the base language: free of
the ledger family `3` and of the projection family `4`, `contract_ledgerFree`,
`contract_projFree`); the three kinds of market; the quote table `a` and the settled-value table
`Y`; and the pins and facts a theorem needs:

* `Y_eq`: the contract settles to the **sibling's own** exact day-`F n` price of `P^{(n)}` —
  `sib n` is a field, any inductor family, *not* pinned to FAF's LIA (the T5 counter-model needs a
  perturbed family);
* `a_eq`: the published quote is `A`'s day-`n` **expectation of the contract LUV**
  `C_n = ledgerLuv 0 n` of `A`'s language, an exact rational. At FAF's LIA the expectation is a
  rational (`li-coupled-pair`'s `liaHistory_expect_eq_machine`, FAF's `expectQuoteAt`); the
  carrier takes the rational as data;
* `A_inductor`: `A` is an inductor over `DPA0 ⊕ (contract ledger settled to Y at σ)` — the ledger
  records `Y n` under every item index (consistent duplicates; `determinedA` speaks of item `0`,
  the contract of record), exactly as in `SealedSiblingSystem`;
* `Hplus_inductor`: the advised reasoner is an inductor over `base ⊕ (two-item ledger: a at eq,
  Y at eY)`;
* `sib_inductor`: sibling `N` is an inductor over the same ledger **frozen at day `N`**
  (`li-coupled-pair`'s `siblingProcess`: quotes of days `≥ N` never injected);
* `hworld*`: every stage of each process is satisfiable (the guard against FAF's
  `isLogicalInductor_of_stage_unsatisfiable`);
* `determined*`: the ledger LUVs are determined at the recorded values (`A`'s contract at `Y n`;
  `Hplus`'s items at the table; the sibling's items of days `< N` at the table, nothing for
  `≥ N`).

**Carrier, not claim**: nothing is asserted. Two-way: `A` reads the siblings (through `Y`), the
siblings and `Hplus` read `A` (through `a`). Existence is the OPEN row `frozenSystem_exists`
(`OffG.lean` §F); the one-way instances are `offGSystem` (`OffG.lean`), `onGSystem` and
`antiSystem` (`OnG.lean`).
Source: [[frozen-deliberation-deference-v6]] §3–§6 (anson-016/017); [[deference-in-logical-induction-v6]] §5.2 (root-deference-036/037); vq-wiki-067; mandate D1
Kind: D
Fidelity: variant: exact rational contract and quote (no grid rounding); plain trader class (FAF's `EfficientlyComputable`); two publication items on the `H`-side (quote and settled value); `D_A ⊇ D` as `shared`
Hyps: n/a (a structure) -/
structure FrozenSystem where
  /-- The shared world process `D` (the weaker reasoner's and every sibling's base). -/
  base : DeductiveProcess
  /-- The predictor's base process `D_A` (before the contract ledger). -/
  DPA0 : DeductiveProcess
  /-- `D_A ⊇ D`: every stage of the shared process is a subset of the predictor's base stage. -/
  shared : ∀ n, base.D n ⊆ DPA0.D n
  /-- Publication of the quote `a n` into the `H`-side ledger (item `0`). -/
  eq : PublicationSchedule
  /-- Publication of the settled value `Y n` into the `H`-side ledger (item `1`). -/
  eY : PublicationSchedule
  /-- The horizon `F`: the sibling is read at day `F n`. -/
  F : DeferralFunction
  /-- Settlement of the contract into the predictor's process. -/
  σ : PublicationSchedule
  /-- The quote is published before the horizon. -/
  eq_lt_F : ∀ n, eq.e n < F.f n
  /-- The horizon precedes settlement. -/
  F_lt_σ : ∀ n, F.f n < σ.e n
  /-- The settled value reaches the `H`-side no earlier than settlement. -/
  σ_le_eY : ∀ n, σ.e n ≤ eY.e n
  /-- The contract propositions `P^{(n)}`. -/
  contract : ℕ → Sentence
  /-- The contract family is e.c. (FAF's `MachineSentenceCodes`). -/
  contract_codes : MachineSentenceCodes contract
  /-- The contracts are free of the ledger family `3` (base language). -/
  contract_ledgerFree : ∀ n, TagFreeSentence (cleanroomBaseTag + ledgerFamily) (contract n)
  /-- The contracts are free of the projection family `4` (for T7 off `G`). -/
  contract_projFree : ∀ n, TagFreeSentence (cleanroomBaseTag + 4) (contract n)
  /-- The predictor `A`. -/
  A : History
  /-- The advised reasoner `H⁺`. -/
  Hplus : History
  /-- The sealed siblings `H^{[N]}`. -/
  sib : ℕ → History
  /-- The published quote table `a n = 𝔼^A_n(C_n)`. -/
  a : ℕ → ℚ
  /-- The settled values `Y n`. -/
  Y : ℕ → ℚ
  /-- The contract settles to the sibling's exact day-`F n` price of `P^{(n)}`. -/
  Y_eq : ∀ n, (Y n : ℝ) = sib n (F.f n) (contract n)
  /-- The quote is `A`'s day-`n` expectation of the contract LUV `C_n = ledgerLuv 0 n`. -/
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
  /-- `A`'s contract LUV `C_n` is determined, in `A`'s process, at `Y n`. -/
  determinedA : ∀ n, LUV.DeterminedVia (ledgerLuv 0 n)
    (ledgerProcess DPA0 (fun _ n => Y n) (fun _ => σ)) (Y n)
  /-- Every `H`-side ledger LUV is determined, in `H⁺`'s process, at the table. -/
  determinedH : ∀ j n, LUV.DeterminedVia (ledgerLuv j n)
    (ledgerProcess base (frozenTable a Y) (frozenSched eq eY)) (frozenTable a Y j n)
  /-- In sibling `N`, the ledger LUVs of days `n < N` are determined at the table; nothing for
  `n ≥ N`. -/
  determinedSib : ∀ N j n, n < N → LUV.DeterminedVia (ledgerLuv j n)
    (siblingProcess base (frozenTable a Y) (frozenSched eq eY) N) (frozenTable a Y j n)

namespace FrozenSystem

/-- The predictor's process `D_A ⊕ (contract ledger settled to Y at σ)`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev processA (S : FrozenSystem) : DeductiveProcess :=
  ledgerProcess S.DPA0 (fun _ n => S.Y n) (fun _ => S.σ)

/-- The advised reasoner's process `D ⊕ (quote at eq, settled value at eY)`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev processH (S : FrozenSystem) : DeductiveProcess :=
  ledgerProcess S.base (frozenTable S.a S.Y) (frozenSched S.eq S.eY)

/-- Sibling `N`'s process: the advised reasoner's ledger frozen at day `N` (`D ⊕ Q^{<N}`).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev processSib (S : FrozenSystem) (N : ℕ) : DeductiveProcess :=
  siblingProcess S.base (frozenTable S.a S.Y) (frozenSched S.eq S.eY) N

/-- The `[0,1]` range of the settled values, read off `determinedA` and `hworldA`
(`def-tracking-pin`'s `determinedVia_mem_Icc`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem Y_mem_Icc (S : FrozenSystem) (n : ℕ) : 0 ≤ S.Y n ∧ S.Y n ≤ 1 := by
  have h := Cleanroom.Deference.DefTrackingPin.determinedVia_mem_Icc (S.determinedA n) S.hworldA
  exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩

/-- The `[0,1]` range of the published quotes: `A`'s expectation of a LUV lies in `[0,1]`
(FAF's `price_mem_Icc` through `expectApprox`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem a_mem_Icc (S : FrozenSystem) (n : ℕ) : 0 ≤ S.a n ∧ S.a n ≤ 1 := by
  haveI := S.A_inductor
  have hP : ∀ m φ, 0 ≤ S.A m φ ∧ S.A m φ ≤ 1 := fun m φ =>
    IsLogicalInductor.price_mem_Icc (P := S.A) (DP := S.processA) m φ
  have h0 := (ledgerLuv 0 n).expectApprox_nonneg (S.A n) (n + 1) (fun s => (hP n s).1)
  have h1 := (ledgerLuv 0 n).expectApprox_le_one (S.A n) (n + 1) (fun s => (hP n s).2)
  have ha := S.a_eq n
  rw [LUV.expect] at ha
  exact ⟨by exact_mod_cast ha ▸ h0, by exact_mod_cast ha ▸ h1⟩

/-- Every stage of the shared process is contained in the corresponding stage of the predictor's
process, the advised reasoner's process and every sibling's process (`bli-found`'s `extendBy`
adjoins; `shared` for `A`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem base_subset_processA (S : FrozenSystem) (n : ℕ) : S.base.D n ⊆ S.processA.D n :=
  (S.shared n).trans (by
    show S.DPA0.D n ⊆ S.DPA0.D n ∪ _
    exact Finset.subset_union_left)

/-- `base_subset_processH`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem base_subset_processH (S : FrozenSystem) (n : ℕ) : S.base.D n ⊆ S.processH.D n := by
  show S.base.D n ⊆ S.base.D n ∪ _
  exact Finset.subset_union_left

/-- `base_subset_processSib`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem base_subset_processSib (S : FrozenSystem) (N n : ℕ) :
    S.base.D n ⊆ (S.processSib N).D n := by
  show S.base.D n ⊆ S.base.D n ∪ _
  exact Finset.subset_union_left

/-- A world consistent with every stage of a process containing the shared process stage-wise is
consistent with every stage of the shared process.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem consistentWithTheory_base_of_subset {S : FrozenSystem} {DP : DeductiveProcess}
    (hsub : ∀ n, S.base.D n ⊆ DP.D n) {w : PCWorld} (hw : w.ConsistentWithTheory DP) :
    w.ConsistentWithTheory S.base :=
  fun n φ hφ => hw n φ (hsub n hφ)

end FrozenSystem

/-! ## C. D2: the fragments, defined from the processes -/

/-- **Decided by the horizon** (the first clause of membership in `G`): `P^{(n)}` or its negation
lies in stage `F n` of the shared process. **Stage membership, syntactic**: FAF's
`DeductiveProcess.D` has no closure, so a sentence provable from the stage but not in it is not
"decided" here; every completed-theory world holds it nonetheless (`holds_of_mem_stage`), which is
all the theorems use.
Source: [[frozen-deliberation-deference-v6]] §6 ("`P^{(n)}` settles in `D` by stage `F(n)`"); mandate D2
Kind: D
Fidelity: variant: stage membership for the source's "settles in `D`"
Hyps: n/a -/
def DecidedBy (S : FrozenSystem) (n : ℕ) : Prop :=
  S.contract n ∈ S.base.D (S.F.f n) ∨ ∼S.contract n ∈ S.base.D (S.F.f n)

/-- **The decided value** `𝟙(P^{(n)})`, read off stage `F n`: `1` if `P^{(n)}` is in the stage,
else `0`. **Junk** off `DecidedBy` (then it is `0` with no meaning) and when a stage holds both
polarities (then no world is consistent with the stage and every statement below about worlds is
vacuous); every use sits under `DecidedBy`.
Source: [[frozen-deliberation-deference-v6]] §6 ("truth"); mandate D2
Kind: D
Fidelity: exact under `DecidedBy`
Hyps: n/a -/
def truthAt (S : FrozenSystem) (n : ℕ) : ℚ :=
  if S.contract n ∈ S.base.D (S.F.f n) then 1 else 0

/-- **The timely fragment `G`** (D2): decided by the horizon, and the sibling's verdict within the
tolerance `ε n` of the decided value. `ε : ℕ → ℚ` is a parameter, not a field, so that
monotonicity and non-vacuity can be stated across tolerances.
Source: [[frozen-deliberation-deference-v6]] §6 ("Timely `G` — `P^{(n)}` settles in `D` by stage `F(n)` *and* `|Y_n − truth| ≤ εₙ`"); mandate D2
Kind: D
Fidelity: exact (stage membership for "settles")
Hyps: n/a -/
def Timely (S : FrozenSystem) (ε : ℕ → ℚ) (n : ℕ) : Prop :=
  DecidedBy S n ∧ |S.Y n - truthAt S n| ≤ ε n

/-- Decided at some stage of the shared process (the complement of "undecidable").
Source: [[frozen-deliberation-deference-v6]] §6
Kind: D
Fidelity: exact (stage membership)
Hyps: n/a -/
def DecidedAt (S : FrozenSystem) (n : ℕ) : Prop :=
  ∃ m, S.contract n ∈ S.base.D m ∨ ∼S.contract n ∈ S.base.D m

/-- **The slow fragment**: decided at some stage, but not timely (either decided only after the
horizon, or decided by it with the verdict outside the tolerance).
Source: [[frozen-deliberation-deference-v6]] §6 ("Slow — decidable but not settled-and-converged by `F(n)`")
Kind: D
Fidelity: exact
Hyps: n/a -/
def Slow (S : FrozenSystem) (ε : ℕ → ℚ) (n : ℕ) : Prop := DecidedAt S n ∧ ¬ Timely S ε n

/-- **The undecidable fragment**: never decided at any stage of the shared process.
Source: [[frozen-deliberation-deference-v6]] §6 ("Undecidable — never settles")
Kind: D
Fidelity: exact
Hyps: n/a -/
def Undecidable (S : FrozenSystem) (n : ℕ) : Prop := ¬ DecidedAt S n

/-- Decided by the horizon implies decided at some stage.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem DecidedBy.decidedAt {S : FrozenSystem} {n : ℕ} (h : DecidedBy S n) : DecidedAt S n :=
  ⟨S.F.f n, h⟩

/-- **The partition lemma**: every index lies in exactly one of the three fragments.
Source: [[frozen-deliberation-deference-v6]] §6 ("Every index `n` falls in exactly one fragment")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem fragments_partition (S : FrozenSystem) (ε : ℕ → ℚ) (n : ℕ) :
    (Timely S ε n ∨ Slow S ε n ∨ Undecidable S n) ∧
      ¬ (Timely S ε n ∧ Slow S ε n) ∧ ¬ (Timely S ε n ∧ Undecidable S n) ∧
      ¬ (Slow S ε n ∧ Undecidable S n) := by
  refine ⟨?_, fun h => h.2.2 h.1, fun h => h.2 h.1.1.decidedAt, fun h => h.2 h.1.1⟩
  by_cases hT : Timely S ε n
  · exact Or.inl hT
  by_cases hD : DecidedAt S n
  · exact Or.inr (Or.inl ⟨hD, hT⟩)
  · exact Or.inr (Or.inr hD)

/-- Membership in `G` is decidable (the stage is a finite set of sentences, the tolerance clause a
rational comparison): `inferInstance`. Its computability as a function of `n` (the mandate's
`Computable` form) is `timely_computable` (`Computable.lean`, repair round 1), for a shared
process computable in FAF's sense and computable contracts, horizon, diagonal and tolerance; that
membership is decidable but not FP is finding F1.
Source: [[frozen-deliberation-deference-v6]] §6 ("Membership is decidable"); mandate D2
Kind: L
Fidelity: exact
Hyps: n/a -/
instance decidedBy_decidable (S : FrozenSystem) (n : ℕ) : Decidable (DecidedBy S n) := by
  unfold DecidedBy; infer_instance

/-- `timely_decidable`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
instance timely_decidable (S : FrozenSystem) (ε : ℕ → ℚ) (n : ℕ) : Decidable (Timely S ε n) := by
  unfold Timely; infer_instance

/-- **Target-Soundness on `G` is the definition**: the second conjunct of `Timely`. Kind D/T, no
headline row (mandate T5: "on `G`, TS is a theorem — and needs nothing about the family"; the
content on `G` is T7's exactness, `Limits.lean`).
Source: [[frozen-deliberation-deference-v6]] §Target-Soundness ("By definition of `G`, `|Y_n − 𝟙(P^{(n)})| ≤ εₙ → 0`")
Kind: T
Fidelity: exact (it is the definition)
Hyps: (a) none -/
theorem timely_tolerance {S : FrozenSystem} {ε : ℕ → ℚ} {n : ℕ} (h : Timely S ε n) :
    |S.Y n - truthAt S n| ≤ ε n := h.2

/-! ### The decided value in every completed-theory world -/

/-- **`truthAt_holds`, base form**: under `DecidedBy`, every world consistent with every stage of
the shared process holds `P^{(n)}` iff `truthAt S n = 1`. No consistency hypothesis is needed for
this per-world form (a stage holding both polarities has no consistent world, so the statement is
vacuous there); the global non-vacuity `∃ v, v.ConsistentWithTheory base` is what makes the
theorems that quantify over such worlds say something; it is derived from the carrier
(`FrozenSystem.base_theoryWorld`, `Engine.lean`), not carried as a hypothesis.
Source: mandate D2 (`truthAt_holds`); FAF `PCWorld.ConsistentWithTheory.holds_of_mem_stage`
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem truthAt_holds {S : FrozenSystem} {n : ℕ} (h : DecidedBy S n) {w : PCWorld}
    (hw : w.ConsistentWithTheory S.base) : w.Holds (S.contract n) ↔ truthAt S n = 1 := by
  unfold truthAt
  by_cases hmem : S.contract n ∈ S.base.D (S.F.f n)
  · rw [if_pos hmem]
    exact ⟨fun _ => rfl, fun _ => hw.holds_of_mem_stage ⟨_, hmem⟩⟩
  · rw [if_neg hmem]
    have hneg : ∼S.contract n ∈ S.base.D (S.F.f n) := h.resolve_left hmem
    have := hw.holds_of_mem_stage ⟨_, hneg⟩
    rw [PCWorld.holds_neg] at this
    exact ⟨fun hh => absurd hh this, fun h1 => absurd h1 (by norm_num)⟩

/-- Under `DecidedBy`, `truthAt S n ∈ {0, 1}`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem truthAt_eq_zero_or_one (S : FrozenSystem) (n : ℕ) : truthAt S n = 0 ∨ truthAt S n = 1 := by
  unfold truthAt; split_ifs <;> simp

/-- The payout of `P^{(n)}` in a completed-theory world of the shared process is the decided value.
Source: mandate D2 (`truthAt_holds`), payout form
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem payout_contract_eq_truthAt {S : FrozenSystem} {n : ℕ} (h : DecidedBy S n) {w : PCWorld}
    (hw : w.ConsistentWithTheory S.base) : w.payout (S.contract n) = (truthAt S n : ℝ) := by
  unfold PCWorld.payout
  rcases truthAt_eq_zero_or_one S n with h0 | h1
  · rw [if_neg (fun hh => by have := (truthAt_holds h hw).1 hh; rw [h0] at this; norm_num at this),
      h0]
    simp
  · rw [if_pos ((truthAt_holds h hw).2 h1), h1]
    simp

/-- **`truthAt_holds` in the predictor's process**: every completed-theory world of `A`'s process
holds `P^{(n)}` iff `truthAt S n = 1` (through `shared` and the ledger adjunction).
Source: mandate D2 ("and the same in `DPA0`")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem truthAt_holds_A {S : FrozenSystem} {n : ℕ} (h : DecidedBy S n) {w : PCWorld}
    (hw : w.ConsistentWithTheory S.processA) : w.Holds (S.contract n) ↔ truthAt S n = 1 :=
  truthAt_holds h (S.consistentWithTheory_base_of_subset S.base_subset_processA hw)

/-- **`truthAt_holds` in the advised reasoner's process.**
Source: mandate D2 ("in `Hplus`'s … process")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem truthAt_holds_H {S : FrozenSystem} {n : ℕ} (h : DecidedBy S n) {w : PCWorld}
    (hw : w.ConsistentWithTheory S.processH) : w.Holds (S.contract n) ↔ truthAt S n = 1 :=
  truthAt_holds h (S.consistentWithTheory_base_of_subset S.base_subset_processH hw)

/-- **`truthAt_holds` in every sibling's process.**
Source: mandate D2 ("in every sibling's process")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem truthAt_holds_sib {S : FrozenSystem} {n : ℕ} (h : DecidedBy S n) (N : ℕ) {w : PCWorld}
    (hw : w.ConsistentWithTheory (S.processSib N)) :
    w.Holds (S.contract n) ↔ truthAt S n = 1 :=
  truthAt_holds h (S.consistentWithTheory_base_of_subset (S.base_subset_processSib N) hw)

/-- A completed-theory world that holds `ψ` values FAF's indicator LUV `𝟙(ψ)` at `1`
(`def-tracking-pin`'s `indicatorOf_valuesAt_one`, re-proved here so that this file does not
import that package's heavy `Column` module; the statement is theirs).
Source: none: infrastructure (FAF `LUV.indicatorOf_isIndicator`; `def-tracking-pin` `Column.lean`)
Kind: L
Fidelity: n/a -/
theorem indicatorOf_valuesAt_one' {DP : DeductiveProcess} {w : PCWorld}
    (hw : w.ConsistentWithTheory DP) {ψ : Sentence} (hψ : w.Holds ψ) :
    w.ValuesAt (LUV.indicatorOf ψ) 1 := by
  refine ⟨zero_le_one, le_rfl, fun r => ⟨fun hr => ?_, fun hr => ?_⟩⟩
  · obtain ⟨h0, h01, _⟩ := LUV.indicatorOf_isIndicator ψ DP w hw r
    by_cases hr0 : (r : ℝ) < 0
    · exact h0 hr0
    · exact (h01 (not_lt.1 hr0) hr).2 hψ
  · exact (LUV.indicatorOf_isIndicator ψ DP w hw r).2.2 hr.le

/-- A completed-theory world that does not hold `ψ` values `𝟙(ψ)` at `0` (`def-tracking-pin`'s
`indicatorOf_valuesAt_zero`, re-proved for the same reason).
Source: none: infrastructure (FAF `LUV.indicatorOf_isIndicator`; `def-tracking-pin` `Column.lean`)
Kind: L
Fidelity: n/a -/
theorem indicatorOf_valuesAt_zero' {DP : DeductiveProcess} {w : PCWorld}
    (hw : w.ConsistentWithTheory DP) {ψ : Sentence} (hψ : ¬ w.Holds ψ) :
    w.ValuesAt (LUV.indicatorOf ψ) 0 := by
  refine ⟨le_rfl, zero_le_one, fun r => ⟨fun hr => ?_, fun hr => ?_⟩⟩
  · exact (LUV.indicatorOf_isIndicator ψ DP w hw r).1 hr
  · obtain ⟨_, h01, h1⟩ := LUV.indicatorOf_isIndicator ψ DP w hw r
    by_cases hr1 : (r : ℝ) < 1
    · exact fun h => hψ ((h01 hr.le hr1).1 h)
    · exact h1 (not_lt.1 hr1)

/-- **`truthAt_holds`, indicator-LUV form**: under `DecidedBy`, every completed-theory world of a
process containing the shared process stage-wise values `𝟙(P^{(n)})` at `truthAt S n`.
Source: mandate D2 ("values `indicatorOf (contract n)` at `truthAt n`")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem indicator_contract_valuesAt {S : FrozenSystem} {n : ℕ} (h : DecidedBy S n)
    {DP : DeductiveProcess} (hsub : ∀ m, S.base.D m ⊆ DP.D m) {w : PCWorld}
    (hw : w.ConsistentWithTheory DP) :
    w.ValuesAt (LUV.indicatorOf (S.contract n)) (truthAt S n : ℝ) := by
  have hb := S.consistentWithTheory_base_of_subset hsub hw
  rcases truthAt_eq_zero_or_one S n with h0 | h1
  · rw [h0]
    push_cast
    exact indicatorOf_valuesAt_zero' hw (fun hh => by
      have := (truthAt_holds h hb).1 hh; rw [h0] at this; norm_num at this)
  · rw [h1]
    push_cast
    exact indicatorOf_valuesAt_one' hw ((truthAt_holds h hb).2 h1)

/-! ## D. D3: the on-`G` statement shape -/

/-- **The on-`G'` statement shape of record** (D3): along the zero set of a ruler `t`, the two
real sequences are eventually within every `δ > 0`. Every on-`G` conclusion in this package has
this form, with `t` a `UnaryRuler` and the hypothesis `∀ n, t n = 0 → Timely S ε n` relating the
e.c. sub-fragment to `G` — never a conclusion `∀ n ∈ G, …` of a bound that was assumed, and never a
conclusion about a free set.
Source: mandate D3; `li-projection`'s `decided_fragment_agree_daySet` (the form it uses)
Kind: D
Fidelity: n/a -/
def AgreeAlong (t : ℕ → ℕ) (x y : ℕ → ℝ) : Prop :=
  ∀ δ > 0, ∀ᶠ n in atTop, t n = 0 → |x n - y n| ≤ δ

/-- `AgreeAlong` is symmetric.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem AgreeAlong.symm {t : ℕ → ℕ} {x y : ℕ → ℝ} (h : AgreeAlong t x y) : AgreeAlong t y x := by
  intro δ hδ
  filter_upwards [h δ hδ] with n hn ht
  rw [abs_sub_comm]
  exact hn ht

/-- `AgreeAlong` is transitive (the triangle inequality at `δ/2 + δ/2`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem AgreeAlong.trans {t : ℕ → ℕ} {x y z : ℕ → ℝ} (h₁ : AgreeAlong t x y)
    (h₂ : AgreeAlong t y z) : AgreeAlong t x z := by
  intro δ hδ
  filter_upwards [h₁ (δ / 2) (half_pos hδ), h₂ (δ / 2) (half_pos hδ)] with n hn1 hn2 ht
  calc |x n - z n| ≤ |x n - y n| + |y n - z n| := abs_sub_le _ _ _
    _ ≤ δ / 2 + δ / 2 := add_le_add (hn1 ht) (hn2 ht)
    _ = δ := by ring

/-- A global `≈ₙ` restricts to every sub-fragment.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem AgreeAlong.of_asympEq {t : ℕ → ℕ} {x y : ℕ → ℝ} (h : x ≈ₙ y) : AgreeAlong t x y := by
  intro δ hδ
  filter_upwards [asympEq_iff_eventuallyWithin.1 h δ hδ] with n hn _
  exact hn

/-- On a sub-fragment of `G` the verdict is eventually within every `δ` of the decided value, once
the tolerance vanishes: `AgreeAlong t Y truthAt` from `Timely` and `ε → 0`. Kind L — this is the
definition of `G` read asymptotically, not a theorem about the construction.
Source: [[frozen-deliberation-deference-v6]] §6 ("On `G`, `Y_n → truth`"); mandate D2
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem agreeAlong_Y_truthAt (S : FrozenSystem) (ε : ℕ → ℚ) (t : ℕ → ℕ)
    (hG : ∀ n, t n = 0 → Timely S ε n) (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0)) :
    AgreeAlong t (fun n => (S.Y n : ℝ)) (fun n => (truthAt S n : ℝ)) := by
  intro δ hδ
  have h2 : ∀ᶠ n in atTop, |(ε n : ℝ)| ≤ δ := by
    have := hε.abs
    rw [abs_zero] at this
    exact this.eventually (eventually_le_nhds hδ)
  filter_upwards [h2] with n hn ht
  have h := (hG n ht).2
  have h' : |(S.Y n : ℝ) - (truthAt S n : ℝ)| ≤ (ε n : ℝ) := by exact_mod_cast h
  exact h'.trans ((le_abs_self _).trans hn)

/-! ## E. D4: the influence defect and the distance -/

/-- **The influence defect** (root-fa-2-011 (i)): the sibling's verdict against the advised
reasoner's own horizon opinion of `P^{(n)}`, `|Y n − Hplus (F n) (contract n)|`. Definition of
record; the source attaches no theorem to it.
Source: root-fa-2-011 (i)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def defect (S : FrozenSystem) (n : ℕ) : ℝ :=
  |(S.Y n : ℝ) - S.Hplus (S.F.f n) (S.contract n)|

/-- **The off-`G` distance** up to day `N`: the sum of the defects over the days not in `G`.
Definition of record; no theorem is attached in the source.
Source: root-fa-2-011 (i)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def Dist (S : FrozenSystem) (ε : ℕ → ℚ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), if Timely S ε n then 0 else defect S n

/-! ## F. The tolerance schedule, read closely (repair round 2) -/

/-- **A free tolerance is a strict comparison** (audit r2 adversarial N1). Over any two systems
and any day, "there is a non-negative tolerance schedule at which `S` is timely and `S'` is not"
is exactly: `S` is decided and (`S'` is undecided, or `S`'s verdict is strictly closer to its
decided value than `S'`'s is to its own). The schedule `ε m := |Y_m − truthAt m|` of `S`
discharges the "timely for `S`" half for free. This is what the OPEN `timely_not_mono_open`
(`OffG.lean` §F) asks, once its pins are unfolded (`notMono_tol_iff`, `OnG.lean` §G): one day on
which the later-horizon sibling's verdict is strictly farther from the decided value.
Source: audit r2 adversarial N1 (probe `ToleranceFree.lean`); mandate T13
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem exists_tol_iff (S S' : FrozenSystem) (n : ℕ) :
    (∃ ε : ℕ → ℚ, (∀ m, 0 ≤ ε m) ∧ Timely S ε n ∧ ¬ Timely S' ε n) ↔
      (DecidedBy S n ∧
        (¬ DecidedBy S' n ∨ |S.Y n - truthAt S n| < |S'.Y n - truthAt S' n|)) := by
  constructor
  · rintro ⟨ε, -, ⟨hD, hle⟩, hnot⟩
    refine ⟨hD, ?_⟩
    by_cases hD' : DecidedBy S' n
    · right
      by_contra hcon
      exact hnot ⟨hD', (not_lt.1 hcon).trans hle⟩
    · exact Or.inl hD'
  · rintro ⟨hD, h⟩
    refine ⟨fun m => |S.Y m - truthAt S m|, fun m => abs_nonneg _, ⟨hD, le_rfl⟩, ?_⟩
    rintro ⟨hD', hle'⟩
    rcases h with h | h
    · exact h hD'
    · exact absurd hle' (not_le.2 h)

/-- **Diagonal convergence gives the whole on-`G` package at `t ≡ 0`** (repair round 2, audit r2
adversarial B1 (iii)). At a system in which every day is decided by the horizon, if for every
constant tolerance `δ > 0` almost every day is timely (the last conjunct of the OPEN
`timely_cofinite_const`, `OffG.lean` §F — the sibling family converging along its diagonal), then
there is a non-negative tolerance schedule vanishing at infinity at which **every** day is timely:
`ε n := |Y_n − truthAt n|`. So at that system every on-`G` theorem of the package applies with the
trivial ruler `t ≡ 0` (an infinite e.c. sub-fragment) — this is why the nine on-`G` two-way rows
are partial over `timely_cofinite_const` and not over the bare existence row
`frozenSystem_exists`, at whose pin non-emptiness of `G` is not established.
Source: audit r2 adversarial B1 (iii); mandate D2 (non-vacuity of `G`)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem timely_all_of_diagonal (S : FrozenSystem) (hdec : ∀ n, DecidedBy S n)
    (hdiag : ∀ δ : ℚ, 0 < δ → ∀ᶠ n in atTop, Timely S (fun _ => δ) n) :
    ∃ ε : ℕ → ℚ, Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0) ∧ (∀ n, 0 ≤ ε n) ∧
      ∀ n, Timely S ε n := by
  refine ⟨fun n => |S.Y n - truthAt S n|, ?_, fun n => abs_nonneg _, fun n => ⟨hdec n, le_rfl⟩⟩
  rw [Metric.tendsto_atTop]
  intro r hr
  obtain ⟨δ, hδ0, hδr⟩ := exists_rat_btwn hr
  have hδ0' : (0 : ℚ) < δ := by exact_mod_cast hδ0
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hdiag δ hδ0')
  refine ⟨N, fun n hn => ?_⟩
  have h := (hN n hn).2
  have h1 : ((|S.Y n - truthAt S n| : ℚ) : ℝ) ≤ (δ : ℝ) := by exact_mod_cast h
  have h0 : (0 : ℝ) ≤ ((|S.Y n - truthAt S n| : ℚ) : ℝ) := by exact_mod_cast abs_nonneg _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
  exact h1.trans_lt hδr

end Cleanroom.Deference.DefFrozenSibling
