import Cleanroom.Li.LiCoupledPair.B.Clocked
import Cleanroom.Found.LiQuoteLane.Ledger
import Cleanroom.Found.LiQuoteLane.Codes
import LogicalInduction.Construction.Conditioning.Endpoints
import LogicalInduction.Construction.Quotation.MarketQuoteCodes

/-!
# `li-coupled-pair` · B · Conditioned: `A` reads `H` by conditioning on the clocked ledger

Angle B's rendering of the `A`-reads-`H` direction ([[li-coupled-pair-mandate]], T1 by the
conditioning route). `A`'s base is any inductor `P` over `DPA0`; `A` itself is FAF's conditioned
market `conditionedHistory P ψ` (`thm:scon`, `lic_conditioned_growing_ofSequence`) on the growing
conjunction of the **clocked quote sequence** `ψ := clockedSeq c₁ σ` (`Clocked.lean`), whose
literals record `H`'s realized day-`f n` expectations of `XH n` as `li-quote-lane`'s ledger LUV
`ledgerLuv 0 n`; `A`'s process is `DPA0 ∪ prefixProcess ψ`, so the literal at position `t` is in
stage `t` — **timed**, which the Σ₁ discharge (angle A) is not, and which `li-quote-lane`'s mirror
ledger is only at a stage the publisher chooses rather than one the computation pays for.

**What is proved here, and at what grade.**

* `clocked_inductor` — `A` is a logical inductor over the clocked process. Kind C (FAF's
  `thm:scon` at the clocked sequence), hypotheses **(a) throughout**: the certificate
  `MachineSentenceCodes ψ`, the one `(c)` of li-quote-lane's `conditioningRoute_inductor`, is
  `clockedSeq_codes`. The schedule's own poly-time certificate `hσ` is discharged at the
  witnesses (`succSchedule_ruler`, `payoutSchedule_ruler`).
* `ledgerLuv_determinedVia_clocked` / `crossQuotePackage_clocked` — the cross-market quote
  package (`CrossQuotePackage`, li-quote-lane's Kind-D hypothesis package) is a **theorem** over the
  clocked process for an arbitrary market program `MH` of `H`: every completed-theory world of
  `A`'s process values `ledgerLuv 0 n` at `𝔼^H_{f n}(XH n)`. Kind C, (a).
* `clockedProcess_theoryWorld` / `clockedProcess_hworld` — non-vacuity of the world quantifier
  (the override world of `bli-found`/li-quote-lane, since every literal written is a literal of
  `ledgerSchedule a σ`).
* `clocked_absent_before_schedule` — the timing guarantee the two-way recursion would use: no
  literal of day `n` is in a stage before `(σ j).e n`.

**What is not a two-way pair.** `ConditionedPair` bundles `A := P | ψ_H` reading `H` (timed) with
`H` an inductor over a ledger of `P`'s prices. `H` reads **`P`, `A`'s unconditioned base, not `A`**:
conditioning is a transformation of a *fixed* inductor, so a market `H` that read `A`'s
conditioned prices would have to read a function of its own expectations — the same fixed point
as the plan's `TwoWayPair`, which angle A attacks by the staggered day recursion. This file
does not build it and says so in the structure's docstring (findings).

**Junk values disclosed.** FAF's `conditionalQuote V φ ψ` is `1` when `V ψ = 0` or `V (φ ⋏ ψ) ≥ V ψ`
(`Properties/Conditioning.lean`): `A`'s prices are meaningful where `P` keeps the growing
conjunction at positive price. Nothing here is stated about `A`'s prices themselves; the
criterion (`clocked_inductor`) does not need positivity (as li-quote-lane's `Conditioning.lean`
notes, the source's obligation (iii) is about prices). A positivity statement would go through
`lic_uniform_nonDogmatism_ofCE` and is not attempted.

Scope: one-way timed (`A` reads `H`); bundled with a one-way `H`-reads-`P`.
-/

namespace Cleanroom.Li.LiCoupledPair.B

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiQuoteLane
open Cleanroom.Found.LiAsympCalc
open Nat.Partrec (Code)

attribute [local irreducible] Nat.sqrt

/-! ## A. The clocked process and the conditioned market -/

/-- **`A`'s process**: the base `DPA0` with the clocked quote sequence adjoined stage by stage
(FAF's `prefixProcess`): stage `t` holds `DPA0.D t` and the positions `≤ t` of `clockedSeq c₁ σ`.
Scope: one-way (`A` reads a fixed table).
Source: mandate angle B (`DPA0.union (prefixProcess ψ)`); anson-2-002 (`H⁺ := H | Q_A`, roles swapped)
Kind: D
Fidelity: exact
Hyps: n/a -/
def clockedProcess (DPA0 : DeductiveProcess) (c₁ : Code) (σ : ℕ → PublicationSchedule) :
    DeductiveProcess :=
  DPA0.union (prefixProcess (clockedSeq c₁ σ))

/-- `clockedProcess_D`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma clockedProcess_D (DPA0 : DeductiveProcess) (c₁ : Code)
    (σ : ℕ → PublicationSchedule) (t : ℕ) :
    (clockedProcess DPA0 c₁ σ).D t = DPA0.D t ∪ (prefixProcess (clockedSeq c₁ σ)).D t := rfl

/-- The day-`n` condition: the prefix conjunction `ψ₀ ⋏ ⋯ ⋏ ψₙ` of the clocked sequence (FAF's
`sentenceConjunction`, with its `⊤` terminator).
Source: FAF `lic_conditioned_growing_ofSequence`
Kind: D
Fidelity: exact
Hyps: n/a -/
def clockedCondition (c₁ : Code) (σ : ℕ → PublicationSchedule) (n : ℕ) : Sentence :=
  sentenceConjunction ((List.range (n + 1)).map (clockedSeq c₁ σ))

/-- **The conditioned market `A = P | (ψ₀ ⋏ ⋯ ⋏ ψₙ)`** (FAF's `conditionedHistory`, with its capped
`conditionalQuote`: `1` at a zero-price condition — module docstring).
Source: mandate angle B; FAF `conditionedHistory`
Kind: D
Fidelity: exact (FAF's capped conditional)
Hyps: n/a -/
noncomputable def clockedHistory (P : History) (c₁ : Code) (σ : ℕ → PublicationSchedule) :
    History :=
  conditionedHistory P (clockedCondition c₁ σ)

/-- **`A` is a logical inductor over the clocked process — no certificate hypothesis.** FAF's
`thm:scon` (`lic_conditioned_growing_ofSequence`) at the clocked sequence, whose
`MachineSentenceCodes` premise is the theorem `clockedSeq_codes`. Compare li-quote-lane's
`conditioningRoute_inductor`, which takes the certificate as its `(c)` `hψ`: at the clocked
sequence that clause is gone. Scope: one-way (`A` reads a fixed table); the table is `H`'s
realized expectations in `crossQuotePackage_clocked`.
Source: anson-2-002 (`Lemma [Existence]`, the conditioning construction); mandate angle B; FAF `lic_conditioned_growing_ofSequence`
Kind: L (one application of FAF's endpoint; the content is the certificate `clockedSeq_codes`, Kind P — the grading li-quote-lane's audit gave `conditioningRoute_inductor`)
Fidelity: variant: plain trader class; the source's cost-domination schedule is the clock (FAF's fuel), plus the explicit gate `σ`
Hyps: (a) none (`hσ`: the schedule is poly-time, discharged at the witnesses) -/
theorem clocked_inductor (P : History) (DPA0 : DeductiveProcess) [IsLogicalInductor P DPA0]
    (c₁ : Code) (σ : ℕ → PublicationSchedule)
    (hσ : UnaryRuler fun p => (σ p.unpair.1).e p.unpair.2) :
    IsLogicalInductor (clockedHistory P c₁ σ) (clockedProcess DPA0 c₁ σ) :=
  ConditioningCompile.lic_conditioned_growing_ofSequence P DPA0 (clockedSeq c₁ σ)
    (clockedSeq_codes c₁ σ hσ)

/-- Next-day publication is a poly-time schedule.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma succSchedule_ruler :
    UnaryRuler fun p : ℕ => ((fun _ : ℕ => PublicationSchedule.succ) p.unpair.1).e p.unpair.2 :=
  (UnaryRuler.unpairSnd.add (UnaryRuler.const 1)).of_eq fun _ => rfl

/-- Same-day publication is a poly-time schedule.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sameDaySchedule_ruler :
    UnaryRuler fun p : ℕ => ((fun _ : ℕ => PublicationSchedule.sameDay) p.unpair.1).e p.unpair.2 :=
  UnaryRuler.unpairSnd.of_eq fun _ => rfl

/-! ## B. Determinacy: every ledger LUV is decided at the recorded value -/

/-- A world consistent with every stage of the clocked process affirms `⌜α_{j,n} > r⌝` when
`r < a j n` and denies it when `a j n ≤ r`: the literal is written at some position
(`clockedSeq_eventually`), hence in that stage.
Source: mandate angle B (the route's determinacy, as li-quote-lane T1.2 / `ledgerSeq_decides`)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem clockedSeq_decides {a : ℕ → ℕ → ℚ} (DPA0 : DeductiveProcess) (c₁ : Code)
    (σ : ℕ → PublicationSchedule) (hc : ∀ p, c₁.eval p = Part.some (gateVal a p)) (j n : ℕ)
    (r : ℚ) (v : PCWorld) (hv : v.ConsistentWithTheory (clockedProcess DPA0 c₁ σ)) :
    (r < a j n → v.Holds ((ledgerLuv j n).gt r)) ∧
      (a j n ≤ r → ¬ v.Holds ((ledgerLuv j n).gt r)) := by
  obtain ⟨t, -, ht⟩ := clockedSeq_eventually c₁ σ hc j n (Encodable.encode r) (by simp)
  have hholds : v.Holds (literalOf (ledgerEntry a j n (Encodable.encode r))) := by
    rw [← ht]
    have hmem : clockedSeq c₁ σ t ∈ (clockedProcess DPA0 c₁ σ).D t := by
      rw [clockedProcess_D]
      exact Finset.mem_union_right _ (self_mem_prefixProcess _ le_rfl)
    exact hv t _ hmem
  simp only [ledgerEntry, ratOfCode_encode] at hholds
  constructor
  · intro hr
    rw [decide_eq_true hr, literalOf_true] at hholds
    exact hholds
  · intro hr
    rw [decide_eq_false (not_lt.mpr hr), literalOf_false, PCWorld.holds_neg] at hholds
    exact hholds

/-- **The route's determinacy**: every completed-theory world of the clocked process values
`α_{j,n}` at the recorded number — li-quote-lane T1.2 transported to the clocked process.
Source: mandate angle B; li-quote-lane `ledgerLuv_determinedVia` / `ledgerLuv_determinedVia_conditioned`
Kind: C
Fidelity: exact, with li-quote-lane's disclosures (α) (β)
Hyps: (a) none (`hmem` is the `[0,1]` range of the table) -/
theorem ledgerLuv_determinedVia_clocked {a : ℕ → ℕ → ℚ} (DPA0 : DeductiveProcess) (c₁ : Code)
    (σ : ℕ → PublicationSchedule) (hc : ∀ p, c₁.eval p = Part.some (gateVal a p))
    (hmem : ∀ j n, 0 ≤ a j n ∧ a j n ≤ 1) (j n : ℕ) :
    LUV.DeterminedVia (ledgerLuv j n) (clockedProcess DPA0 c₁ σ) (a j n) := by
  intro v hv
  unfold PCWorld.ValuesAt
  refine ⟨by exact_mod_cast (hmem j n).1, by exact_mod_cast (hmem j n).2, fun r => ?_⟩
  have h := clockedSeq_decides DPA0 c₁ σ hc j n r v hv
  exact ⟨fun hr => h.1 (by exact_mod_cast hr), fun hr => h.2 (by exact_mod_cast hr.le)⟩

/-! ## C. Non-vacuity of the world quantifier -/

/-- Every literal the clocked sequence writes is a literal of `li-quote-lane`'s schedule
`ledgerSchedule a σ` at some stage.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma clockedSeq_literal_mem_ledgerSchedule {a : ℕ → ℕ → ℚ} (c₁ : Code)
    (σ : ℕ → PublicationSchedule) (hc : ∀ p, c₁.eval p = Part.some (gateVal a p)) (t : ℕ) :
    clockedSeq c₁ σ t = ⊤ ∨
      ∃ s x, x ∈ (ledgerSchedule a σ).lits s ∧ clockedSeq c₁ σ t = literalOf x := by
  rcases clockedSeq_cases c₁ σ hc t with h0 | ⟨n, j, c, hd, hs, -, hlit⟩
  · exact Or.inl h0
  · right
    refine ⟨max (max n j) (max c ((σ j).e n)), ledgerEntry a j n c, ?_, hlit⟩
    exact mem_ledgerSchedule_iff.mpr ⟨n, j, c, le_max_of_le_left (le_max_left _ _),
      le_max_of_le_left (le_max_right _ _), le_max_of_le_right (le_max_left _ _),
      le_max_of_le_right (le_max_right _ _), hd, rfl⟩

/-- **Non-vacuity**: under li-quote-lane T1.5's hypotheses (base free of family 3, every stage
satisfiable) the override world of `ledgerProcess_theoryWorld` is consistent with every stage of
the clocked process — each position is `⊤` or a ledger literal of `ledgerSchedule a σ`.
Source: mandate angle B (non-vacuity); li-quote-lane T1.5 / `ledgerConditionedProcess_theoryWorld`
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem clockedProcess_theoryWorld {a : ℕ → ℕ → ℚ} {DPA0 : DeductiveProcess} {c₁ : Code}
    {σ : ℕ → PublicationSchedule} (hc : ∀ p, c₁.eval p = Part.some (gateVal a p))
    (hfree : ProcessFreeOf (ledgerSchedule a σ) DPA0)
    (h : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA0.D n)) :
    ∃ v : PCWorld, v.ConsistentWithTheory (clockedProcess DPA0 c₁ σ) := by
  obtain ⟨w, hw⟩ := ledgerProcess_theoryWorld hfree h
  refine ⟨w, fun t φ hφ => ?_⟩
  rw [clockedProcess_D, Finset.mem_union] at hφ
  rcases hφ with hbase | hpre
  · exact hw t φ (by rw [ledgerProcess_D]; exact Finset.mem_union_left _ hbase)
  · obtain ⟨u, -, rfl⟩ := mem_prefixProcess.mp hpre
    rcases clockedSeq_literal_mem_ledgerSchedule c₁ σ hc u with h0 | ⟨s, x, hx, hlit⟩
    · rw [h0]; exact PCWorld.holds_top w
    · rw [hlit]
      apply hw s
      rw [ledgerProcess_D, Finset.mem_union]
      exact Or.inr (Finset.mem_image.mpr ⟨x, by simpa using hx, rfl⟩)

/-- `hworld` for the clocked process (the per-stage form).
Source: mandate angle B (non-vacuity)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem clockedProcess_hworld {a : ℕ → ℕ → ℚ} {DPA0 : DeductiveProcess} {c₁ : Code}
    {σ : ℕ → PublicationSchedule} (hc : ∀ p, c₁.eval p = Part.some (gateVal a p))
    (hfree : ProcessFreeOf (ledgerSchedule a σ) DPA0)
    (h : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA0.D n)) :
    ∀ n, ∃ v : PCWorld, v.ConsistentWith ((clockedProcess DPA0 c₁ σ).D n) :=
  let ⟨v, hv⟩ := clockedProcess_theoryWorld hc hfree h
  fun n => ⟨v, hv n⟩

/-! ## D. Timing: nothing before the schedule -/

/-- A position carrying a family-3 literal carries it for its own payload, and only once the
schedule has published that payload's day.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma freshAtom_payload_inj {f p q : ℕ} (h : freshAtom f p = freshAtom f q) : p = q := by
  have h' := congrArg (fun φ : Sentence => match φ with
    | Formula.atom a => (Nat.unpair a).2 | _ => 0) h
  simpa [freshAtom] using h'

/-- A family-3 literal is never `⊤`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma literalOf_ne_top (p : ℕ) (b : Bool) : literalOf (ledgerFamily, p, b) ≠ ⊤ := by
  cases b
  · intro h
    rw [literalOf_false] at h
    change Formula.imp (freshAtom ledgerFamily p) Formula.falsum =
      Formula.imp Formula.falsum Formula.falsum at h
    exact absurd (Formula.imp.inj h).1 (by simp [freshAtom])
  · intro h
    rw [literalOf_true] at h
    change freshAtom ledgerFamily p = Formula.imp Formula.falsum Formula.falsum at h
    simp [freshAtom] at h

/-- A position carrying a family-3 literal carries it for its own payload, and only once the
schedule has published that payload's day.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma clockedSeq_eq_literal_imp (c₁ : Code) (σ : ℕ → PublicationSchedule) (t p : ℕ) (b : Bool)
    (h : clockedSeq c₁ σ t = literalOf (ledgerFamily, p, b)) :
    p = posPayload t ∧ (σ (posItem t)).e (posDay t) ≤ t := by
  unfold clockedSeq at h
  split_ifs at h with hs h2 h1
  · refine ⟨?_, hs⟩
    cases b
    · exact absurd h (by simp [literalOf, freshAtom, Formula.neg_def])
    · exact (freshAtom_payload_inj (by simpa [literalOf] using h)).symm
  · refine ⟨?_, hs⟩
    cases b
    · rw [literalOf_false, Formula.neg_inj] at h
      exact (freshAtom_payload_inj h).symm
    · exact absurd h (by simp [literalOf, freshAtom, Formula.neg_def])
  · exact absurd h.symm (literalOf_ne_top p b)
  · exact absurd h.symm (literalOf_ne_top p b)

/-- **Nothing is in a stage before its publication stage**: a family-3 literal of day `n`, item
`j` is absent from every stage `s < (σ j).e n` of the clocked prefix process. This is the timing a
two-way recursion needs (`A`'s day-`t` stage reads no day-`≥ t` data when `f n < (σ j).e n`); it
is stated for the record and used by no theorem here.
Source: mandate T5.1 (the staggering condition), angle B
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem clocked_absent_before_schedule (c₁ : Code) (σ : ℕ → PublicationSchedule) (j n c s : ℕ)
    (b : Bool) (hs : s < (σ j).e n) :
    literalOf (ledgerFamily, ledgerPayload j n c, b) ∉ (prefixProcess (clockedSeq c₁ σ)).D s := by
  intro hmem
  obtain ⟨t, hts, ht⟩ := mem_prefixProcess.mp hmem
  obtain ⟨hp, hgate⟩ := clockedSeq_eq_literal_imp c₁ σ t _ b ht
  have hday : posDay t = n := by
    rw [posDay, ← hp, ledgerPayload]; simp
  have hitem : posItem t = j := by
    rw [posItem, ← hp, ledgerPayload]; simp
  rw [hday, hitem] at hgate
  omega

/-! ## E. The cross-market quote package, discharged by conditioning -/

/-- **A program for the polarity of `H`'s realized expectations exists**: the table
`n ↦ 𝔼^H_{f n}(XH n)` (FAF's exact rational `expectQuoteAt`) is computable from `XH`'s e.c.
certificate (`expectQuoteAt_computable`) and `f`'s (`DeferralFunction.computable`), so
`gateCode_exists` applies.
Source: none: infrastructure; FAF `MarketComputation.expectQuoteAt_computable`
Kind: L
Fidelity: n/a -/
theorem quoteGateCode_exists {H : History} (MH : MarketComputation H) (XH : ℕ → LUV)
    (hX : LUV.MachineThresholdCodeSeq XH) (f : DeferralFunction) :
    ∃ c₁ : Code, ∀ p, c₁.eval p =
      Part.some (gateVal (fun _ n => MH.expectQuoteAt XH n (f.f n)) p) :=
  gateCode_exists
    (((MH.expectQuoteAt_computable hX).comp
      (Computable.snd.pair (f.computable.comp Computable.snd))).of_eq fun _ => rfl : _)

/-- **T1 by conditioning (headline): the cross-market quote package is a theorem over the clocked
process**, for an arbitrary history `H` with a market program `MH`, an arbitrary base `DPA0` and an
arbitrary polarity program `c₁` for the table of `H`'s realized expectations: the family
`n ↦ ledgerLuv 0 n` is e.c. (li-quote-lane T1.3) and every completed-theory world of
`DPA0 ∪ prefixProcess (clockedSeq c₁ σ)` values it at `𝔼^H_{f n}(XH n)`. **Timed**: the literal
of day `n` is in `A`'s stage at the clocked position, never before `(σ 0).e n`
(`clocked_absent_before_schedule`). Compare angle A's Σ₁ discharge (determinacy via the
completed theory, no stage bound) and li-quote-lane's mirror ledger (a stage the publisher
chooses, but the certificate for conditioning on it was a `(c)`). The package carries no world:
pair it with `clockedProcess_hworld`. Scope: one-way (`A` reads `H`).
Source: [[faithful-acceleration]] §4(II) (root-fa-002, (A2)/(A3)); anson-2-014; [[deference-in-logical-induction-v6]] §5.2; mandate T1.1, angle B
Kind: C
Fidelity: variant: timed, ledger-recorded determinacy (the literal is adjoined by the clocked prefix process) in place of `Γ_A`-provable determinacy; (c) count zero
Hyps: (a) none (`hc` says `c₁` computes the table's polarity; `quoteGateCode_exists` supplies one) -/
theorem crossQuotePackage_clocked {H : History} (MH : MarketComputation H) (XH : ℕ → LUV)
    (f : DeferralFunction) (DPA0 : DeductiveProcess) (c₁ : Code)
    (hc : ∀ p, c₁.eval p = Part.some (gateVal (fun _ n => MH.expectQuoteAt XH n (f.f n)) p))
    (σ : ℕ → PublicationSchedule) :
    CrossQuotePackage H (clockedProcess DPA0 c₁ σ) f XH (fun n => ledgerLuv 0 n) := by
  refine ⟨ledgerLuv_thresholdCodes 0, fun n => ?_⟩
  rw [MH.expectQuoteAt_cast XH n (f.f n)]
  exact ledgerLuv_determinedVia_clocked DPA0 c₁ σ hc
    (fun _ n => MH.expectQuoteAt_mem_Icc XH n (f.f n)) 0 n

/-! ## F. The bundle: `A = P | ψ_H` reads `H`; `H` reads `P` -/

/-- **The conditioned pair** — angle B's carrier. `A := clockedHistory P c₁ σ` is `P` conditioned
on the clocked record of `H`'s realized day-`f n` expectations of `XH n`, an inductor over the
clocked process (`A_inductor`, derived, (a)); the quote package holds there (`package`, (a));
`H` is an inductor over a ledger of **`P`'s** prices of `quotedA` (`H_inductor`) with its
determinacy and world (`determinedH`, `hworldH`).

**Scope: not the plan's two-way pair.** `A` reads `H` (timed: `clocked_absent_before_schedule`);
`H` reads `P` — `A`'s *unconditioned base* — not `A`. Conditioning transforms a fixed inductor, so
a market that read the conditioned `A` would read a function of its own expectations: the fixed
point `TwoWayPair` names and angle A's staggered recursion attacks. The bundle is one-way timed
in each of its two directions, with the two directions meeting at `P`, and is tagged so. Every
field is derived by `ConditionedPair.ofLIA` (`ConditionedWitness.lean`).
Source: mandate angle B; [[deference-in-logical-induction-v6]] §5.2 (root-deference-037); anson-017
Kind: D
Fidelity: variant: `A = P | ψ_H` with `H` reading `P`; plain trader class; FAF's capped conditional quote
Hyps: n/a (a structure) -/
structure ConditionedPair where
  /-- `A`'s base process. -/
  DPA0 : DeductiveProcess
  /-- `H`'s base process. -/
  DPH0 : DeductiveProcess
  /-- What `H` reads of `P`: item `j`, day `n`. -/
  quotedA : ℕ → ℕ → Sentence
  /-- `H`'s publication schedules for `P`'s prices. -/
  e : ℕ → PublicationSchedule
  /-- The LUVs whose realized expectations `A` reads. -/
  XH : ℕ → LUV
  /-- The deferral: `A` reads `H`'s day-`f n` expectation of `XH n`. -/
  f : DeferralFunction
  /-- The schedule gate on `A`'s record of `H`. -/
  σ : ℕ → PublicationSchedule
  /-- `A`'s base inductor. -/
  P : History
  /-- The reader `H`. -/
  H : History
  /-- `H`'s market program. -/
  MH : MarketComputation H
  /-- The polarity program for `H`'s realized expectations. -/
  c₁ : Code
  /-- `c₁` computes the table's polarity. -/
  hc : ∀ p, c₁.eval p = Part.some (gateVal (fun _ n => MH.expectQuoteAt XH n (f.f n)) p)
  /-- `P`'s price table of the quoted sentences. -/
  aP : ℕ → ℕ → ℚ
  /-- The table is `P`'s prices. -/
  aP_eq : ∀ j n, (aP j n : ℝ) = P n (quotedA j n)
  /-- `P` is an inductor over `DPA0`. -/
  P_inductor : IsLogicalInductor P DPA0
  /-- `A = P | ψ_H` is an inductor over the clocked process. -/
  A_inductor : IsLogicalInductor (clockedHistory P c₁ σ) (clockedProcess DPA0 c₁ σ)
  /-- `H` is an inductor over the ledger of `P`'s prices. -/
  H_inductor : IsLogicalInductor H (ledgerProcess DPH0 aP e)
  /-- The quote package: `A`'s process determines `H`'s realized expectations. -/
  package : CrossQuotePackage H (clockedProcess DPA0 c₁ σ) f XH (fun n => ledgerLuv 0 n)
  /-- Every stage of `A`'s process has a world. -/
  hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((clockedProcess DPA0 c₁ σ).D n)
  /-- Every stage of `H`'s process has a world. -/
  hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((ledgerProcess DPH0 aP e).D n)
  /-- `H`'s ledger LUVs are determined at `P`'s prices. -/
  determinedH : ∀ j n, LUV.DeterminedVia (ledgerLuv j n) (ledgerProcess DPH0 aP e) (aP j n)

/-- The conditioned market of a conditioned pair.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable abbrev ConditionedPair.A (p : ConditionedPair) : History :=
  clockedHistory p.P p.c₁ p.σ

/-- `A`'s process of a conditioned pair.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev ConditionedPair.processA (p : ConditionedPair) : DeductiveProcess :=
  clockedProcess p.DPA0 p.c₁ p.σ

/-- `H`'s process of a conditioned pair.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev ConditionedPair.processH (p : ConditionedPair) : DeductiveProcess :=
  ledgerProcess p.DPH0 p.aP p.e

/-! ## G. Citation rows (T2.1) -/

/-- **T2.1, citation row: built fresh needs only `ComputableDeductiveProcess`.** FAF's
`LIA_is_logical_inductor DP hDP` asks for a unary-time program printing the stages — no
polynomial clause — and nothing else. Restated here so the dichotomy of anson-2-007 (i)/(ii) has
both poles as named declarations: fresh = `ComputableDeductiveProcess` (this row); conditioned =
`MachineSentenceCodes` of the conditioning sequence (`conditioned_needs_machineCodes`), which
`clockedSeq_codes` meets for the clocked record of any table.
Source: anson-2-007 (chat 04 L686–703, the fresh/conditioned dichotomy); mandate T2.1; FAF `LIA_is_logical_inductor`
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem fresh_needs_computable (DP : DeductiveProcess) (hDP : ComputableDeductiveProcess DP) :
    IsLogicalInductor (liaHistory DP) DP :=
  LIA_is_logical_inductor DP hDP

/-- **T2.1, citation row: conditioned needs the sentence certificate.** FAF's `thm:scon` for a
growing sequence asks for `MachineSentenceCodes ψ` of the conditioning sequence and nothing about
the values the literals record; this is the obligation anson-2-007 (ii) prices as `σ ≥ R(F(n))`,
and `clockedSeq_codes` discharges it by making the position pay the fuel.
Source: anson-2-007; mandate T2.1; FAF `lic_conditioned_growing_ofSequence`
Kind: L
Fidelity: exact
Hyps: (a) none (the certificate is the theorem's premise, not a hypothesis of this package) -/
theorem conditioned_needs_machineCodes (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (ψ : ℕ → Sentence) (hψ : MachineSentenceCodes ψ) :
    IsLogicalInductor
      (conditionedHistory P (fun n => sentenceConjunction ((List.range (n + 1)).map ψ)))
      (DP.union (prefixProcess ψ)) :=
  ConditioningCompile.lic_conditioned_growing_ofSequence P DP ψ hψ

end Cleanroom.Li.LiCoupledPair.B
