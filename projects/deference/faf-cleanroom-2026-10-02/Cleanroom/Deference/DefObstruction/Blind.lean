import Cleanroom.Deference.DefObstruction.Tracking

/-!
# `def-obstruction` · Blind: the dichotomy "predictable iff uninfluenced", well-posed half (T8)

**Reflective blindness, of record.** A sentence is **blind** for `(DPH, e)` if its settlement in
the reader's completed theory does not depend on the published table: for all tables `a`, `a'`,
it is decided true over `ledgerProcess DPH a e` iff over `ledgerProcess DPH a' e`, and the same
for its negation (`BlindSentence`); a family is blind if every member is (`Blind`). This is the
semantic rendering of the source's "`∂D_A/∂A = 0`": the settlement map factors through `A`-free
data.

**Theorems.** A tag-free family is truth-value blind (`blind_of_tagFree`, by `li-quote-lane`'s
conservativity in both directions); the diagonal is not (`gDiag_not_blind`: the all-`0` and
all-`1` tables settle `g_n` oppositely); hence a blind family contains no `g_n`
(`blind_avoids_diagonal`); and tracking on a family that contains the diagonal infinitely often
fails (`dichotomy_2a_half`, T2 restated on the family's own indicator LUVs).

**Two senses of "blind", kept apart (repair round 2, fidelity B1).** `BlindSentence` is
*truth-value* blindness: table-independence of the family's decidedness in the advised reader's
completed theory. The source's blindness (§4.1) is of the *settlement map* `n ↦ m*_n`, which
encodes the advised reader's **credence** `Y_n = H⁺_{F(n)}(P^{(n)})`; § E states it as
`SettlementBlind`. The two agree on the diagonal (not blind either way: `gDiag_not_blind`; on
FAF's LIA the credence streams of two tables differ, `gDiag_credence_table_dependent` in
`BlindWitness.lean`) and **part on quote-free families over the advised reader**: the Lean calls
them blind (`blind_of_tagFree`, trivially — conservativity twice), the source calls them *not*
blind, because `Y_n` "depends on `A`'s run through the ledger `H⁺` has absorbed by `F(n)`,
whatever `P^{(n)}` is" (§2.5, §4.2: 2b's case). So `blind_of_tagFree` renders only the "2a's
instance is structurally absent" half of §4.3, not "the autonomous target is blind": §4.3's
repair is a change of *reader* (`Y_n := H_{F(n)}(P^{(n)})`, `H` never reads `A`), not of family,
and its blindness is `autonomousTarget_settlementBlind` (§ E) — true by construction, since the
autonomous map mentions no table. The source's "not blind" verdict on quote-free families over
`H⁺` is a claim about the LIA's actual prices on undecided sentences, which no criterion theorem
decides in either direction (findings F-Dichotomy).

**The source's Theorem 4.2 is not statable.** "Provable from a satisfiable power assumption" is
meta-level. What is shipped is `predictable_imp_uninfluenced`, instantiated: the first conjunct
`Tracks → ¬ QuoteRef` is **proved** (2a); the second `SatPower → Blind` rests on the **named,
disclosed hypothesis** `h2b : ¬ Blind → ¬ SatPower` with `SatPower` an opaque `Prop` — 2b is not
a theorem over FAF. **What 2a does and does not give** (findings F-Dichotomy): the earlier Lean's
first conjunct `QuoteRef → Tracks → Blind` has a contradictory antecedent once 2a is instantiated
(`dichotomy_2a_half`), so it is vacuous; the well-posed 2a half is `Tracks → ¬ QuoteRef`, which
is *weaker* than `Tracks → Blind` — a family can avoid `g_n` and still fail to be blind — and
that gap is exactly where 2b lives. **The gap is inhabited** (§ D, repair round 1): the positive
ledger literal `posLit n` ("the quote exceeds `½`") is not `QuoteRef` (syntactic identity with
`gDiag n` fails) and not `Blind` (`gap_inhabited`); `QuoteRef` is a syntactic predicate and
`Tracks → ¬ QuoteRef` says nothing about this quote-dependent family. The hypothesis package of
`gDiag_not_blind` is instantiated at the paper process (`gDiag_not_blind_paper`).

Scope: one-way throughout.
-/

namespace Cleanroom.Deference.DefObstruction

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiQuoteLane
open Cleanroom.Found.LiAsympCalc Cleanroom.Li.LiDiagonal
open Filter Topology

/-! ## A. Blindness of record -/

/-- **A truth-value blind sentence** for `(DPH, e)`: its decidedness (true, and false) in the
advised reader's completed theory is the same for every published table. Truth-value rendering
of "`∂D_A/∂A = 0`"; the source's settlement-map (credence) sense is `SettlementBlind` (§ E), and
the two part on quote-free families (module docstring). Quantifies over every rational table,
not only `[0,1]`-valued ones: the ledger schedule is functional for any table, so no stage goes
unsatisfiable, and the carrier's `range` is the narrower class (audit r2 N5).
Scope: one-way.
Source: [[self-referential-settlement-target]] §4.1 (Definition, reflective blindness; anson-006); [[deference-in-logical-induction-v6]] §4.4
Kind: D
Fidelity: variant: truth-value (table-independence of completed-theory decidedness) in place of the source's "the settlement map factors through `A`-free data", which is about the credence `Y_n`
Hyps: n/a -/
def BlindSentence (DPH : DeductiveProcess) (e : ℕ → PublicationSchedule) (φ : Sentence) : Prop :=
  ∀ a a' : ℕ → ℕ → ℚ,
    ((∀ v : PCWorld, v.ConsistentWithTheory (ledgerProcess DPH a e) → v.Holds φ) ↔
      (∀ v : PCWorld, v.ConsistentWithTheory (ledgerProcess DPH a' e) → v.Holds φ)) ∧
    ((∀ v : PCWorld, v.ConsistentWithTheory (ledgerProcess DPH a e) → v.Holds (∼ φ)) ↔
      (∀ v : PCWorld, v.ConsistentWithTheory (ledgerProcess DPH a' e) → v.Holds (∼ φ)))

/-- **A truth-value blind contract family**: every member is blind.
Scope: one-way.
Source: [[self-referential-settlement-target]] §4.1 (anson-006)
Kind: D
Fidelity: variant: truth-value (as `BlindSentence`)
Hyps: n/a -/
def Blind (DPH : DeductiveProcess) (e : ℕ → PublicationSchedule) (C : ℕ → Sentence) : Prop :=
  ∀ n, BlindSentence DPH e (C n)

/-- **A tag-free sentence is truth-value blind**: the ledger extension is conservative over the
base language for every table (`ledgerProcess_conservative`), so decidedness is the base's,
whatever is published. **What this is not** (repair round 2, fidelity B1): in the source's sense
— blindness of the settlement map, i.e. of the advised reader's credence `Y_n = H⁺_{F(n)}(P^{(n)})`
— quote-free families over the advised reader are *not* blind ([[self-referential-settlement-target]]
§2.5, §4.2: 2b's case, "the dependence runs through `H⁺`'s absorbed ledger, whatever `P^{(n)}`
is"); this theorem is the "2a's instance is structurally absent" half of §4.3 only. The §4.3
repair proper is a change of *reader*, not of family (`autonomousTarget_settlementBlind`, § E).
Scope: one-way.
Source: [[self-referential-settlement-target]] §4.3 (anson-006), the "2a dodged: no contract can encode `𝟙[a_n ≤ ½]`" clause; `li-quote-lane` `ledgerProcess_conservative` (anson-012)
Kind: L (conservativity applied twice)
Fidelity: variant: truth-value blindness — table-independence of the family's decidedness in the advised reader's completed theory — in place of the source's blindness of the settlement map (the credence); on this theorem's own subject the source's verdict is the opposite (not blind: 2b's case)
Hyps: (a) none -/
theorem blindSentence_of_tagFree {DPH : DeductiveProcess} {e : ℕ → PublicationSchedule}
    (hDPH : TagFreeProcess (cleanroomBaseTag + ledgerFamily) DPH)
    {φ : Sentence} (hφ : TagFreeSentence (cleanroomBaseTag + ledgerFamily) φ) :
    BlindSentence DPH e φ := by
  intro a a'
  have hfree : ∀ b : ℕ → ℕ → ℚ, ProcessFreeOf (ledgerSchedule b e) DPH :=
    fun _ => processFreeOf_ledgerSchedule_of_tagFree hDPH
  constructor
  · rw [ledgerProcess_conservative (hfree a) hφ, ledgerProcess_conservative (hfree a') hφ]
  · rw [ledgerProcess_conservative (hfree a) hφ.neg,
      ledgerProcess_conservative (hfree a') hφ.neg]

/-- **A tag-free family is truth-value blind** (headline 4, the quote-free-family half): every
member is, by `blindSentence_of_tagFree`. Not "the autonomous target is blind" — §4.3's sentence
is about a different reader (`autonomousTarget_settlementBlind`, § E) — and not blindness in the
source's credence sense, in which the source classifies this very family as *not* blind (§2.5,
§4.2); see `blindSentence_of_tagFree`.
Scope: one-way.
Source: [[self-referential-settlement-target]] §4.3 (anson-006), the "2a's instance is structurally absent" clause; root-deference-027; lean-deference-015
Kind: L (conservativity applied twice)
Fidelity: variant: truth-value blindness (as `blindSentence_of_tagFree`); the source's verdict on quote-free families over the advised reader is the opposite
Hyps: (a) none -/
theorem blind_of_tagFree {DPH : DeductiveProcess} {e : ℕ → PublicationSchedule}
    (hDPH : TagFreeProcess (cleanroomBaseTag + ledgerFamily) DPH)
    (C : ℕ → Sentence) (hC : ∀ n, TagFreeSentence (cleanroomBaseTag + ledgerFamily) (C n)) :
    Blind DPH e C :=
  fun n => blindSentence_of_tagFree hDPH (hC n)

/-- The all-zero table.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def zeroTable : ℕ → ℕ → ℚ := fun _ _ => 0

/-- The all-one table.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def oneTable : ℕ → ℕ → ℚ := fun _ _ => 1

/-- **The diagonal is not blind**: over the all-`0` table `g_n` holds in every completed world,
over the all-`1` table it fails in every completed world (and there is one:
`ledgerProcess_theoryWorld`).
Scope: one-way.
Source: [[self-referential-settlement-target]] §4.1 ("the self-referential target violates blindness"); root-deference-027
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem gDiag_not_blindSentence {DPH : DeductiveProcess} {e : ℕ → PublicationSchedule}
    (hDPH : TagFreeProcess (cleanroomBaseTag + ledgerFamily) DPH)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n)) (n : ℕ) :
    ¬ BlindSentence DPH e (gDiag n) := by
  intro hB
  have h := (hB zeroTable oneTable).1
  have hL : ∀ v : PCWorld, v.ConsistentWithTheory (ledgerProcess DPH zeroTable e) →
      v.Holds (gDiag n) :=
    fun v hv => (gDiag_truth_iff_table DPH zeroTable e n v hv).2 (by norm_num [zeroTable])
  have hR := h.mp hL
  obtain ⟨w, hw⟩ := ledgerProcess_theoryWorld (a := oneTable) (e := e)
    (processFreeOf_ledgerSchedule_of_tagFree hDPH) hworld
  have h2 := (gDiag_truth_iff_table DPH oneTable e n w hw).1 (hR w hw)
  norm_num [oneTable] at h2

/-- **The diagonal family is not blind.**
Scope: one-way.
Source: [[self-referential-settlement-target]] §4.1 (anson-006); root-deference-027
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem gDiag_not_blind {DPH : DeductiveProcess} {e : ℕ → PublicationSchedule}
    (hDPH : TagFreeProcess (cleanroomBaseTag + ledgerFamily) DPH)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n)) :
    ¬ Blind DPH e gDiag :=
  fun hB => gDiag_not_blindSentence hDPH hworld 0 (hB 0)

/-- **A blind family contains no `g_n`** (root-deference-027's trivial fragment).
Scope: one-way.
Source: [[self-referential-settlement-target]] §4.2 (the quote-referencing case); root-deference-027
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem blind_avoids_diagonal {DPH : DeductiveProcess} {e : ℕ → PublicationSchedule}
    (hDPH : TagFreeProcess (cleanroomBaseTag + ledgerFamily) DPH)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (C : ℕ → Sentence) (hB : Blind DPH e C) : ∀ n, C n ≠ gDiag n := by
  intro n h
  have := hB n
  rw [h] at this
  exact gDiag_not_blindSentence hDPH hworld n this

/-! ## B. Tracking on a family and the quote-referencing predicate -/

/-- **Tracking on a contract family**: the published table asymptotically equals the reader's
day-`F n` expectation of the family's own indicator LUVs, `a ≈ₙ 𝔼^H_{F n}(𝟙 C_n)`.
Scope: one-way.
Source: [[self-referential-settlement-target]] §1 (universal pointwise timely Tracking over the enumeration `P^{(n)}`); mandate T8
Kind: D
Fidelity: exact (FAF's `AsympEq`; the family's indicator LUVs)
Hyps: n/a -/
def TracksFamily (T : TablePair) (F : DeferralFunction) (C : ℕ → Sentence) : Prop :=
  (fun n => (T.a 0 n : ℝ)) ≈ₙ (fun n => (LUV.indicatorOf (C n)).expect T.H (F n))

/-- **A quote-referencing family**: one that contains the diagonal `g_n` infinitely often. (A
single occurrence would carry no asymptotic content; "eventually" is the stronger special case.)
**Syntactic**: it tests identity with `gDiag n`, not quote-dependence — the positive ledger
literal `posLit n` ("the quote exceeds `½`") escapes it while depending on the quote
(`posLit_not_quoteRef`, `posLit_not_blind`, § D). So `Tracks → ¬ QuoteRef` is weaker than "a
trackable family does not reference the quote" (repair round 1, audit N3). **Index-aligned** as
well (audit r2 N2): it demands the diagonal sentence *of the same day*, so a re-indexed diagonal
`n ↦ gDiag (n + 1)`, or any `gDiag ∘ k` with `k n ≠ n`, is `¬ QuoteRef` although every member is
a diagonal sentence. The alignment is right for `dichotomy_2a_half` (the family's day-`F n`
credence is `Y n` only when `C n = gDiag n`; a re-indexed diagonal read at `F n` is a price
Lemma B says nothing about), but `Tracks → ¬ QuoteRef` must not be read as "a trackable family
contains no diagonal sentence".
Scope: one-way.
Source: [[self-referential-settlement-target]] §2.5, §4.2 ("the effective family may reference quotes"); mandate T8 (`QuoteRef`)
Kind: D
Fidelity: variant: "contains `g_n` infinitely often" for "may reference quotes"; syntactic (the positive literal escapes it)
Hyps: n/a -/
def QuoteRef (C : ℕ → Sentence) : Prop := ∃ᶠ n in atTop, C n = gDiag n

/-- The diagonal family is quote-referencing.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem quoteRef_gDiag : QuoteRef gDiag :=
  (Eventually.of_forall fun _ => rfl).frequently

/-- Tracking on the diagonal family is `a ≈ₙ Y`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem tracksFamily_gDiag_iff (T : TablePair) (F : DeferralFunction) :
    TracksFamily T F gDiag ↔ ((fun n => (T.a 0 n : ℝ)) ≈ₙ T.Y F) := Iff.rfl

/-- **The 2a half of the dichotomy**: on a family containing the diagonal infinitely often,
tracking fails (T2 restated: on those days the family's credence *is* `Y_n`, and the defect
there is at least `¼` eventually, so `a − 𝔼^H_{F n}(𝟙 C_n)` does not tend to `0`).
Scope: one-way; deferral `F` (injective).
Source: [[self-referential-settlement-target]] §4.2 (the quote-referencing branch of Theorem 4.2's proof); anson-006; mandate T8 (`dichotomy_2a_half`)
Kind: L (restatement of `tracking_fails`)
Fidelity: exact
Hyps: (c) `hR`, `hR'`, `hG` (the cost model); `hf` — scope: injective deferral -/
theorem dichotomy_2a_half (T : TablePair) (F : DeferralFunction) (hf : Function.Injective F.f)
    (hR : MachineSentenceCodes (padTrueSide T.a F))
    (hR' : MachineSentenceCodes (padFalseSide T.a F))
    (hG : MachineSentenceCodes (padG F))
    (C : ℕ → Sentence) (hC : QuoteRef C) : ¬ TracksFamily T F C := by
  intro h
  unfold TracksFamily AsympEq at h
  have h1 : Tendsto (fun n => |(T.a 0 n : ℝ) - (LUV.indicatorOf (C n)).expect T.H (F n)|)
      atTop (𝓝 0) := by simpa using h.abs
  have h2 := h1.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 / 4 by norm_num))
  have h3 := tracking_fails T F hf hR hR' hG (1 / 4) (by norm_num)
  obtain ⟨n, hn, hn2, hn3⟩ := (hC.and_eventually (h2.and h3)).exists
  have hn2' : |(T.a 0 n : ℝ) - (LUV.indicatorOf (C n)).expect T.H (F n)| < 1 / 4 := hn2
  have heq : (LUV.indicatorOf (C n)).expect T.H (F n) = T.Y F n := by
    rw [hn]; rfl
  rw [heq] at hn2'
  linarith

/-- **Blind ⟹ not quote-referencing** (the trivial direction of the gap between the two).
Scope: one-way.
Source: root-deference-027
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem not_quoteRef_of_blind {DPH : DeductiveProcess} {e : ℕ → PublicationSchedule}
    (hDPH : TagFreeProcess (cleanroomBaseTag + ledgerFamily) DPH)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (C : ℕ → Sentence) (hB : Blind DPH e C) : ¬ QuoteRef C :=
  not_frequently.mpr (Eventually.of_forall (blind_avoids_diagonal hDPH hworld C hB))

/-! ## C. The dichotomy, instantiated -/

/-- **"Predictable iff uninfluenced", instantiated (headline 4).** Over a table-only pair with the
cost-model certificates, for any contract family `C` and any proposition `SatPower` ("the power
assumption is satisfiable"):
* `Tracks → ¬ QuoteRef` — **proved** from 2a (`dichotomy_2a_half`): a family one can track
  avoids the diagonal;
* `SatPower → Blind` — from the **named hypothesis** `h2b : ¬ Blind → ¬ SatPower`, which is
  obstruction 2b and **is not a theorem over FAF** (FAF has one trader class and no resource
  model; findings F-2b). This conjunct is kind `L` and discloses that.
The source's "blindness is derived" holds only in the 2a half, and there only as "the diagonal is
avoided", which is weaker than blindness (module docstring; findings F-Dichotomy).
Scope: one-way; deferral `F` (injective).
Source: [[self-referential-settlement-target]] §4.2 Theorem 4.2 (anson-006); [[deference-in-logical-induction-v6]] §4.4; `SelfReferentialTarget.lean:predictable_imp_uninfluenced` ([[AUDIT]] §3.5, the propositional silhouette this instantiates)
Kind: L (the 2a conjunct is a restatement of `tracking_fails`; the 2b conjunct is plumbing over the named `h2b`)
Fidelity: variant: `QuoteRef` as "contains `g_n` infinitely often"; `Blind` semantic; `SatPower` opaque
Hyps: (c) `hR`, `hR'`, `hG` (the cost model); `hf` — scope: injective deferral; (b)/(c) `h2b` — obstruction 2b taken as a named hypothesis, not a theorem over FAF -/
theorem predictable_imp_uninfluenced (T : TablePair) (F : DeferralFunction)
    (hf : Function.Injective F.f)
    (hR : MachineSentenceCodes (padTrueSide T.a F))
    (hR' : MachineSentenceCodes (padFalseSide T.a F))
    (hG : MachineSentenceCodes (padG F))
    (C : ℕ → Sentence) (SatPower : Prop) (h2b : ¬ Blind T.DPH T.e C → ¬ SatPower) :
    (TracksFamily T F C → ¬ QuoteRef C) ∧ (SatPower → Blind T.DPH T.e C) :=
  ⟨fun ht hq => dichotomy_2a_half T F hf hR hR' hG C hq ht,
    fun hp => by_contra fun hb => h2b hb hp⟩

/-! ## D. The gap between `¬ QuoteRef` and `Blind`, inhabited; the paper-process instance -/

/-- **The positive ledger literal**: "the day-`n` quote is `> ½`" — `gDiag n` is its negation.
Source: audit r1 probe `PositiveLiteralNotBlind`; findings F-Dichotomy (the gap sentence)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def posLit (n : ℕ) : Sentence := (ledgerLuv 0 n).gt (1 / 2)

/-- Syntactically never the diagonal (an atom is not an implication).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem posLit_ne_gDiag (n : ℕ) : posLit n ≠ gDiag n := by
  intro h
  rw [gDiag_eq, LO.NegAbbrev.neg] at h
  simp only [posLit, ledgerLuv_gt, freshAtom] at h
  cases h

/-- **The positive literal is not quote-referencing in the package's sense.**
Source: audit r1 probe `PositiveLiteralNotBlind`
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem posLit_not_quoteRef : ¬ QuoteRef posLit :=
  not_frequently.mpr (Eventually.of_forall posLit_ne_gDiag)

/-- **Yet it is not blind**: the all-one table decides it true, the all-zero table decides it
false.
Scope: one-way.
Source: audit r1 probe `PositiveLiteralNotBlind`; findings F-Dichotomy
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem posLit_not_blind {DPH : DeductiveProcess} {e : ℕ → PublicationSchedule}
    (hDPH : TagFreeProcess (cleanroomBaseTag + ledgerFamily) DPH)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n)) :
    ¬ Blind DPH e posLit := by
  intro hB
  have h := (hB 0 oneTable zeroTable).1
  have hL : ∀ v : PCWorld, v.ConsistentWithTheory (ledgerProcess DPH oneTable e) →
      v.Holds (posLit 0) := by
    intro v hv
    have hg := gDiag_truth_iff_table DPH oneTable e 0 v hv
    have hng : ¬ v.Holds (gDiag 0) := fun hh => by
      have := hg.1 hh
      norm_num [oneTable] at this
    rw [gDiag_eq, PCWorld.holds_neg] at hng
    exact not_not.mp hng
  have hR := h.mp hL
  obtain ⟨w, hw⟩ := ledgerProcess_theoryWorld (a := zeroTable) (e := e)
    (processFreeOf_ledgerSchedule_of_tagFree hDPH) hworld
  have hg0 : w.Holds (gDiag 0) :=
    (gDiag_truth_iff_table DPH zeroTable e 0 w hw).2 (by norm_num [zeroTable])
  rw [gDiag_eq, PCWorld.holds_neg] at hg0
  exact hg0 (hR w hw)

/-- **The gap between the 2a half and blindness is inhabited**: `posLit` is not quote-referencing
(so `Tracks → ¬ QuoteRef` says nothing about it) and not blind. "A family can avoid `g_n` and
still fail to be blind" (F-Dichotomy (ii)), by the simplest quote-dependent family.
Scope: one-way.
Source: [[self-referential-settlement-target]] §4.2 (the gap 2b's "quote-free families" clause is about); findings F-Dichotomy; audit r1 probe `PositiveLiteralNotBlind`
Kind: N+ (for the gap: a non-constant, quote-dependent family)
Fidelity: exact
Hyps: (a) none -/
theorem gap_inhabited {DPH : DeductiveProcess} {e : ℕ → PublicationSchedule}
    (hDPH : TagFreeProcess (cleanroomBaseTag + ledgerFamily) DPH)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n)) :
    ¬ QuoteRef posLit ∧ ¬ Blind DPH e posLit :=
  ⟨posLit_not_quoteRef, posLit_not_blind hDPH hworld⟩

/-- **The paper-process instance of headline 4's hypothesis package**: `paperDP 𝗜𝚺₁` is tag-free
for the ledger family and has satisfiable stages, so `gDiag_not_blind` and `gap_inhabited` hold
there with no hypothesis (repair round 1, audit N8: the package never instantiated `hDPH`).
Scope: one-way.
Source: mandate T8; audit r1 probe `PositiveLiteralNotBlind` (`gap_inhabited_paper`)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem gDiag_not_blind_paper :
    ¬ Blind (paperDP 𝗜𝚺₁) (fun _ => PublicationSchedule.succ) gDiag ∧
    (¬ QuoteRef posLit ∧ ¬ Blind (paperDP 𝗜𝚺₁) (fun _ => PublicationSchedule.succ) posLit) :=
  ⟨gDiag_not_blind (paperDP_tagFree 𝗜𝚺₁ (Nat.le_add_right _ _)) (paperDP_hworld 𝗜𝚺₁),
    gap_inhabited (paperDP_tagFree 𝗜𝚺₁ (Nat.le_add_right _ _)) (paperDP_hworld 𝗜𝚺₁)⟩

/-! ## E. The source's blindness, of record: the settlement map and the autonomous target

Repair round 2 (fidelity B1). The source's §4.1 blindness is of the *settlement map* — the value
written to settle `C_n`, as a function of the published table — and that value encodes the
reader's deferred credence. `SettlementBlind` states it; `autonomousTarget_settlementBlind` is
§4.3's "the autonomous target is blind", true by construction because the change of reader
removes the table from the map. The credence-level non-blindness of the diagonal on FAF's LIA is
`gDiag_credence_table_dependent` (`BlindWitness.lean`). -/

/-- **Settlement blindness** (the source's §4.1 sense, as a definition of record): a settlement
map `m : (ℕ → ℕ → ℚ) → ℕ → ℝ` — the value written to settle `C_n`, as a function of the published
table — is blind if it does not depend on the table. The source's `m*_n` encodes the advised
reader's deferred credence `Y_n = H⁺_{F(n)}(P^{(n)})`, so this is blindness of the *credence*;
`BlindSentence` (§ A) is the truth-value rendering, and the two part on quote-free families over
the advised reader (module docstring).
Scope: one-way.
Source: [[self-referential-settlement-target]] §4.1 (Definition, reflective blindness: "`∂D_A/∂A = 0`", the settlement map factors through `A`-free data; anson-006)
Kind: D
Fidelity: variant: "does not depend on the table" for "factors through `A`-free data" (the extensional consequence; the `A`-free data is left implicit)
Hyps: n/a -/
def SettlementBlind (m : (ℕ → ℕ → ℚ) → ℕ → ℝ) : Prop := ∀ a a' n, m a n = m a' n

/-- **The autonomous target** (§4.3): a reader `H₀` over the base process — one that never reads
the ledger — settles `C_n` to its own deferred expectation `𝔼^{H₀}_{F n}(X_n)`, a map that
mentions no table.
Scope: one-way.
Source: [[self-referential-settlement-target]] §4.3 ("retarget at the autonomous human: `Y_n := H_{F(n)}(P^{(n)})`, `H` never reads `A`"; anson-006)
Kind: D
Fidelity: exact (the source's `n ↦ H_{F(n)}(P^{(n)})`, read as FAF's `expect`)
Hyps: n/a -/
noncomputable def autonomousTarget (H₀ : History) (X : ℕ → LUV) (F : DeferralFunction) :
    (ℕ → ℕ → ℚ) → ℕ → ℝ :=
  fun _ n => (X n).expect H₀ (F n)

/-- **The autonomous target is settlement-blind** — §4.3's "the autonomous target is blind",
stated as what it is: the map does not mention the table, so the proof is `rfl`. This is the
package's only rendering of §4.3's blindness; `blind_of_tagFree` (§ A) renders a different
claim (a quote-free family is *truth-value* blind over the *advised* reader).
Scope: one-way.
Source: [[self-referential-settlement-target]] §4.3 (anson-006, "the autonomous target as the canonical blind instance"); root-deference-027
Kind: L (trivial by construction: the change of reader removes the table from the map)
Fidelity: exact
Hyps: (a) none -/
theorem autonomousTarget_settlementBlind (H₀ : History) (X : ℕ → LUV) (F : DeferralFunction) :
    SettlementBlind (autonomousTarget H₀ X F) :=
  fun _ _ _ => rfl

end Cleanroom.Deference.DefObstruction
