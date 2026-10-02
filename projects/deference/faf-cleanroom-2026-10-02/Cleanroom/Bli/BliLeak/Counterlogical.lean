import LogicalInduction.Construction.Conditioning.Presentation
import LogicalInduction.Framework.Affine
import LogicalInduction.Framework.Machine.SentenceMachine
import LogicalInduction.Properties.Coherence
import LogicalInduction.Properties.AffineCoherence
import LogicalInduction.Properties.Conditioning

/-!
# `bli-leak` · Counterlogical: conditioning on a refuted sentence is not an object (L8)

"The market state if it saw counterfactual digits of `π`" (bli-soto-b-2-022 (ii)) is not an FAF
object. FAF's `thm:scon` conditions an inductor by *adjoining the condition to the deductive
process* (`DeductiveProcess.adjoinSentence`); when the condition `ψ` is refuted by `DP`
(`∼ψ ∈ DP.D N`), the adjoined process has an unsatisfiable stage (`adjoinSentence_stage_unsatisfiable`,
L8.1), and then

* the criterion over it holds **vacuously for every computable market**
  (`counterlogical_criterion_vacuous`, L8.2, from FAF's `isLogicalInductor_of_stage_unsatisfiable`);
  two computable markets differing on every coordinate — the constant markets `0` and `1` — are
  both inductors over it (`counterlogical_two_inductors`);
* the condition's price and every conjunction's price tend to `0` under any inductor over the
  base process (`counterlogical_price_tendsto_zero`, `counterlogical_conj_tendsto_zero`, L8.3),
  and FAF's capped conditional quote returns its **junk value `1`, not `0`**, on a vanishing
  denominator (`conditionedHistory_junk`; findings K9).

The surviving object is an *early state's expectation of a later state* (bli-soto-b-2-022 (iii)) —
`bli-rvc-ui`'s hypothetical marginalization, not this package's target. Soto's "Ω's logical
counterfactual as an undecided conditional" (bli-soto-b-030) is given the one definition it admits
(`omegaQuote`, L8.4) and no theorem that it is "reasonable" (recorded in the findings as ill-posed).

Attributions (Soto's Ω, Abram's replacement) are ATTRIBUTION-UNVETTED.
-/

namespace Cleanroom.Bli.BliLeak

open LogicalInduction LO.Propositional Filter Topology

/-! ## L8.1: a refuted condition makes the adjoined process unsatisfiable -/

/-- **L8.1 (stage form).** If `∼ψ ∈ DP.D N`, no world is consistent with stage `N` of
`DP.adjoinSentence ψ`: it would have to hold both `ψ` (the adjoined stage `{ψ}`) and `∼ψ`.
Source: mandate L8.1; bli-soto-b-2-022 (the FAF finding)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem adjoinSentence_stage_unsatisfiable {DP : DeductiveProcess} {ψ : Sentence} {N : ℕ}
    (hdis : (∼ψ) ∈ DP.D N) :
    ∀ v : PCWorld, ¬ v.ConsistentWith ((DP.adjoinSentence ψ).D N) := by
  intro v hv
  rw [DeductiveProcess.adjoinSentence, PCWorld.consistentWith_union_iff] at hv
  have h1 : v.Holds (∼ψ) := hv.1 _ hdis
  have h2 : v.Holds ψ := hv.2 ψ (Finset.mem_singleton_self ψ)
  rw [PCWorld.holds_neg] at h1
  exact h1 h2

/-- **L8.1 (semantic form).** If `∼ψ ∈ DP.D N`, every world consistent with stage `N` of the
*base* process falsifies `ψ`.
Source: mandate L8.1
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem not_holds_of_neg_mem_stage {DP : DeductiveProcess} {ψ : Sentence} {N : ℕ}
    (hdis : (∼ψ) ∈ DP.D N) :
    ∀ v : PCWorld, v.ConsistentWith (DP.D N) → ¬ v.Holds ψ :=
  fun v hv h => (PCWorld.holds_neg v ψ).mp (hv _ hdis) h

/-- Adjoining a fixed sentence preserves computability of the process (FAF's
`fixedConditionProcessComputation` and `union_toComputable`).
Source: mandate L8.2 (computability of `adjoinSentence`)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem adjoinSentence_computable {DP : DeductiveProcess} (hDP : ComputableDeductiveProcess DP)
    (ψ : Sentence) : ComputableDeductiveProcess (DP.adjoinSentence ψ) :=
  DeductiveProcessComputation.union_toComputable hDP.nonemptyComputation.some
    (fixedConditionProcessComputation ψ)

/-! ## L8.2: the criterion is vacuous -/

/-- **L8.2. Counterlogical conditioning is not an object: the criterion is vacuous.** Over a
computable process `DP` that refutes `ψ` at some stage, **every** computable market is a logical
inductor over `DP.adjoinSentence ψ` — the process FAF's `thm:scon` conditions on `ψ` over. The
criterion says nothing about "the market state if it saw `ψ`".
Scope: vacuous criterion, every computable market; the base process's own consistency at the
refuting stage is carried by `counterlogical_criterion_vacuous_of_consistent` and by the witness
`counterlogical_two_inductors_dayVarying` (`Witnesses.lean`).
Source: mandate L8.2; bli-soto-b-2-022 (ii); [[bli-program]] §4 row L8; FAF
`isLogicalInductor_of_stage_unsatisfiable`
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem counterlogical_criterion_vacuous {DP : DeductiveProcess}
    (hDP : ComputableDeductiveProcess DP) {ψ : Sentence} {N : ℕ} (hdis : (∼ψ) ∈ DP.D N) :
    ∀ V : History, ComputableMarket V → IsLogicalInductor V (DP.adjoinSentence ψ) :=
  fun V hV => isLogicalInductor_of_stage_unsatisfiable V _ hV (adjoinSentence_computable hDP ψ)
    (adjoinSentence_stage_unsatisfiable hdis)

/-- L8.2 with the guard against the trivial case: the base process **is** satisfiable at the
refuting stage (so the unsatisfiability is the adjoined condition's doing, and the conditioning
is genuinely counterlogical), and every computable market is an inductor over the adjoined
process.
Source: mandate L8.2 (trap: "proving vacuity for a `DP` that is unsatisfiable before adjoining")
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem counterlogical_criterion_vacuous_of_consistent {DP : DeductiveProcess}
    (hDP : ComputableDeductiveProcess DP) {ψ : Sentence} {N : ℕ} (hdis : (∼ψ) ∈ DP.D N)
    (hcons : ∃ v : PCWorld, v.ConsistentWith (DP.D N)) :
    (∃ v : PCWorld, v.ConsistentWith (DP.D N) ∧ ¬ v.Holds ψ) ∧
      ∀ V : History, ComputableMarket V → IsLogicalInductor V (DP.adjoinSentence ψ) := by
  obtain ⟨v, hv⟩ := hcons
  exact ⟨⟨v, hv, not_holds_of_neg_mem_stage hdis v hv⟩, counterlogical_criterion_vacuous hDP hdis⟩

/-! ## The two constant markets -/

/-- The constant market at the rational `q`.
Source: mandate L8.2 (witness)
Kind: D
Fidelity: n/a -/
noncomputable def constMarket (q : ℚ) : History := fun _ _ => (q : ℝ)

/-- A constant market in `[0, 1]` is a computable market (the table is the constant `q`).
Source: mandate L8.2 (witness)
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem constMarket_computable {q : ℚ} (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    ComputableMarket (constMarket q) :=
  ComputableMarket.ofComputableTable (fun _ _ => q)
    (fun _ _ => ⟨by show (0 : ℝ) ≤ (q : ℝ); exact_mod_cast h0,
      by show (q : ℝ) ≤ 1; exact_mod_cast h1⟩) (fun _ _ => rfl)
    (Computable.const _)

/-- The constant markets `0` and `1` differ on every day and every sentence.
Source: mandate L8.2 (witness: "two computable markets differing on every day and sentence")
Kind: L
Fidelity: n/a -/
theorem constMarket_zero_ne_one : ∀ n φ, constMarket 0 n φ ≠ constMarket 1 n φ := by
  intro n φ
  simp [constMarket]

/-- **N+ for L8.2, abstract form**: over any computable process refuting `ψ` at a stage it is
itself consistent at, the constant markets `0` and `1` — which disagree everywhere — are both
logical inductors over `DP.adjoinSentence ψ`.
Source: mandate L8.2 (witness)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem counterlogical_two_inductors {DP : DeductiveProcess}
    (hDP : ComputableDeductiveProcess DP) {ψ : Sentence} {N : ℕ} (hdis : (∼ψ) ∈ DP.D N)
    (hcons : ∃ v : PCWorld, v.ConsistentWith (DP.D N)) :
    (∃ v : PCWorld, v.ConsistentWith (DP.D N) ∧ ¬ v.Holds ψ) ∧
      IsLogicalInductor (constMarket 0) (DP.adjoinSentence ψ) ∧
      IsLogicalInductor (constMarket 1) (DP.adjoinSentence ψ) ∧
      ∀ n φ, constMarket 0 n φ ≠ constMarket 1 n φ := by
  obtain ⟨hw, hall⟩ := counterlogical_criterion_vacuous_of_consistent hDP hdis hcons
  exact ⟨hw, hall _ (constMarket_computable le_rfl zero_le_one),
    hall _ (constMarket_computable zero_le_one le_rfl), constMarket_zero_ne_one⟩

/-! ## L8.3: the conditional quote carries no information -/

/-- **L8.3 (i): the junk value.** When the condition's price is `0` (and prices are nonnegative),
FAF's capped conditional quote is `1` — **junk value `1`**, not `0` — for every `φ`.
Source: mandate L8.3 (i); findings K9; FAF `conditionalQuote_eq_one`
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem conditionedHistory_junk {P : History} {n : ℕ} {ψ : Sentence}
    (hP : ∀ φ, 0 ≤ P n φ) (h : P n ψ = 0) :
    ∀ φ, conditionedHistory P (fun _ => ψ) n φ = 1 := by
  intro φ
  unfold conditionedHistory
  exact conditionalQuote_eq_one (by rw [h]; exact hP _)

/-- The conditional quote is the ratio of the conjunction's price to the condition's, capped at
`1` (FAF's definition, restated as a disjunction).
Source: mandate L8.3 ("the quote is a ratio of two vanishing sequences, capped at `1`")
Kind: L
Fidelity: exact -/
theorem conditionedHistory_eq_div_or_one (P : History) (ψ φ : Sentence) (n : ℕ) :
    (P n (φ ⋏ ψ) < P n ψ ∧ conditionedHistory P (fun _ => ψ) n φ = P n (φ ⋏ ψ) / P n ψ) ∨
      (P n ψ ≤ P n (φ ⋏ ψ) ∧ conditionedHistory P (fun _ => ψ) n φ = 1) := by
  unfold conditionedHistory
  by_cases h : P n (φ ⋏ ψ) < P n ψ
  · exact Or.inl ⟨h, conditionalQuote_eq_div h⟩
  · exact Or.inr ⟨not_lt.mp h, conditionalQuote_eq_one (not_lt.mp h)⟩

/-- **L8.3 (ii): the condition's price vanishes.** Under any inductor over `DP`, if `DP` refutes
`ψ` at some stage, `P n ψ → 0` (FAF's `lic_disprovable_tendsto_zero`).
Source: mandate L8.3 (ii); bli-soto-b-2-022 ("`ℙₙ(ψ) → 0` by the LIC")
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem counterlogical_price_tendsto_zero (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (ψ : Sentence) (hdis : ∃ k, (∼ψ) ∈ DP.D k)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ConvergesTo (fun n => P n ψ) 0 :=
  lic_disprovable_tendsto_zero P DP ψ hdis hworld

/-- **L8.3 (ii): every conjunction's price vanishes too.** For every `φ`, `P n (φ ⋏ ψ) ≈ₙ 0`
(FAF's `lic_provind_false` on the constant family `fun _ ↦ φ ⋏ ψ`, whose disprovability is
semantic: a world consistent with the completed theory falsifies `ψ`, hence `φ ⋏ ψ`). So the
conditional quote is a ratio of two vanishing sequences, capped at `1`.
Source: mandate L8.3 (ii)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem counterlogical_conj_tendsto_zero (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (ψ : Sentence) (hdis : ∃ k, (∼ψ) ∈ DP.D k)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (φ : Sentence) :
    (fun n => P n (φ ⋏ ψ)) ≈ₙ fun _ => 0 :=
  lic_provind_false P DP (fun _ => φ ⋏ ψ) (MachineSentenceCodes.const _)
    (fun _ v hv => by
      rw [PCWorld.holds_neg, PCWorld.holds_and]
      rintro ⟨-, hψ⟩
      exact (PCWorld.holds_neg v ψ).mp (hv.holds_of_mem_stage hdis) hψ)
    hworld

/-! ## L8.4: Ω's "latest state not having decided `C`" as an object -/

open Classical in
/-- The first stage at which `DP` decides `C` (either literal in the stage).
Source: mandate L8.4; bli-soto-b-030 (Ω's rule)
Kind: D
Fidelity: variant: "decided" read as stage membership of a literal, the only reading the rule
admits over a `DeductiveProcess` -/
noncomputable def decisionDay (DP : DeductiveProcess) (C : Sentence)
    (h : ∃ k, C ∈ DP.D k ∨ (∼C) ∈ DP.D k) : ℕ :=
  Nat.find h

open Classical in
/-- Ω's "latest state not having decided `C`": the day before the decision day (`0` if `C` is
decided at stage `0` — a junk value the rule does not address).
Source: mandate L8.4; bli-soto-b-030
Kind: D
Fidelity: variant: junk at a stage-`0` decision -/
noncomputable def lastUndecidedDay (DP : DeductiveProcess) (C : Sentence)
    (h : ∃ k, C ∈ DP.D k ∨ (∼C) ∈ DP.D k) : ℕ :=
  decisionDay DP C h - 1

open Classical in
/-- Ω's counterfactual quote: `B` conditioned on `C` at the latest undecided day, through FAF's
capped conditional quote. No theorem that it is "reasonable" is stated: bli-soto-b-030 is
ill-posed there (findings).
Source: mandate L8.4; bli-soto-b-030
Kind: D
Fidelity: variant: FAF's capped quote (junk value `1`) -/
noncomputable def omegaQuote (P : History) (DP : DeductiveProcess) (C B : Sentence)
    (h : ∃ k, C ∈ DP.D k ∨ (∼C) ∈ DP.D k) : ℝ :=
  conditionalQuote (P (lastUndecidedDay DP C h)) B C

open Classical in
/-- At the last undecided day, when the decision day is positive, neither literal of `C` is in the
stage.
Source: mandate L8.4
Kind: L
Fidelity: exact -/
theorem undecided_at_lastUndecidedDay (DP : DeductiveProcess) (C : Sentence)
    (h : ∃ k, C ∈ DP.D k ∨ (∼C) ∈ DP.D k) (hpos : 0 < decisionDay DP C h) :
    C ∉ DP.D (lastUndecidedDay DP C h) ∧ (∼C) ∉ DP.D (lastUndecidedDay DP C h) := by
  have hlt : lastUndecidedDay DP C h < decisionDay DP C h := by
    unfold lastUndecidedDay
    omega
  have := Nat.find_min h hlt
  push Not at this
  exact this

open Classical in
/-- Ω's quote is a genuine ratio iff the conjunction is priced strictly below the condition at
the latest undecided day; otherwise it is the junk value `1`.
Source: mandate L8.4 ("non-junk iff `P m (B ⋏ C) < P m C` at that day")
Kind: L
Fidelity: exact -/
theorem omegaQuote_eq (P : History) (DP : DeductiveProcess) (C B : Sentence)
    (h : ∃ k, C ∈ DP.D k ∨ (∼C) ∈ DP.D k) :
    omegaQuote P DP C B h =
      if P (lastUndecidedDay DP C h) (B ⋏ C) < P (lastUndecidedDay DP C h) C
      then P (lastUndecidedDay DP C h) (B ⋏ C) / P (lastUndecidedDay DP C h) C else 1 := rfl

end Cleanroom.Bli.BliLeak
