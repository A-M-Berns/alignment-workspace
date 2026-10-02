import Cleanroom.Trust.TrustMerge.SelfInstance

/-!
# `trust-merge` · Stretch: non-transitivity stated OPEN; cross-trust is automatic on quoted
estimates (T10, 2-006)

**2-006 (LI non-transitivity).** The lab conjectures inductors `H, A, B` with LUV-Total-Trust
`H → A` and `A → B` but not `H → B`, diagnosing a weight-class mismatch (`A`'s endorsement of `B`
on `A`-generable weights, `H`'s Value on `H`-generable ones). `tt-finite-frames` T3 refutes that
diagnosis at the finite level (its ledger row `T4.totalTrust_not_transitive` and the T3
characterization: the obstruction is cellwise conditional-prior mismatch, not observability), so
the recovery condition is **re-stated here as quotability of the far expert**, with generability
kept as a separate sufficient condition.

* `crossTrust_of_quoted` (L): in the averaged grade, cross-trust toward *any* expert whose estimate
  is reflected by an e.c. quote in the reader's process is automatic from `thm:wubexp`
  (`quoteUnbiased_ofComputation`), given a deadline program — the middle link `A → B` is not
  used. So "recovered iff `B` is `H`-observable" has its `if` half for free at this grade; the
  conjecture's content is entirely in the `only if` (an unquoted `B`), which is the OPEN.
* `li_nontransitivity_open` (OPEN, `sorry`): three inductors, two averaged cross-trust links, the
  long link failing — stated over `LUVTotalTrustAvg` and `def-lattice`'s `Expert`. A construction
  would need `B`'s estimates to be unquotable in `H`'s process while quoted in `A`'s, i.e. a
  language-inclusion or time-hierarchy separation (the same obstruction as `li-quote-lane`'s
  `readability_fails_without_generability`); not attempted.
-/

namespace Cleanroom.Trust.TrustMerge

open LogicalInduction LogicalInduction.FeedbackTruth Filter Topology
open Cleanroom.Found.DefLattice Cleanroom.Found.LiAsympCalc

noncomputable section

/-- **Cross-trust toward a quoted expert is automatic in the averaged grade:** if the reader's
process determines an e.c. quote of the expert's estimate, the reader's expectation of the quote
is `w`-unbiased for it (`thm:wubexp`), with no appeal to any intermediate expert. The `if` half of
2-006's "recovered iff `B` is `H`-observable", at this grade, with the deadline program the one
named hypothesis.
Source: trust-lab-2-006 (the recovery condition, re-stated as quotability); mandate T10
Kind: L (an instance of `quoteUnbiased_ofComputation`)
Fidelity: exact
Hyps: (b) `C` — the deadline program of `thm:wubexp` (an undischarged hypothesis of the cited
theorem, doubly deferred, F-C; no instance exhibited); all else (a) -/
theorem crossTrust_of_quoted {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    (E : Expert DP) (X Y : ℕ → LUV) (hY : LUV.MachineThresholdCodeSeq Y)
    (hR : Reflects DP E X Y) (hstrict : StrictlyIncreasingDeferral E.f)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (C : FeedbackTruthComputation
      (LUVCombination.normalizedMeshTruth (fun n => LUVCombination.ofLUV (Y n)) P DP hworld 1)
      E.f) :
    QuoteUnbiased P DP E X Y :=
  quoteUnbiased_ofComputation E X Y hY hR hstrict hworld C

/-- **The typed OPEN admits a pure clause-(i) failure:** unquotability of the far expert refutes
averaged LUV-Total-Trust outright, so `li_nontransitivity_open` as typed is satisfied by any
triple in which `B`'s estimates are quoted in `A`'s process but not in `H`'s — the `only if`
half of the recovery condition, with no averaged-clause content. The question with content
(clause (i) holding on the long link while the averaged cross-defect fails) is, by
`crossTrust_of_quoted`, a question about the deadline program `C` alone, and is not what is
typed (audit r2 adversarial N5, probe ported; the open-list reason says so).
Source: audit r2 adversarial N5 (probe `NontransitivityByUnquotability.lean`)
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem not_luvTotalTrustAvg_of_not_observable {P : History} {DP : DeductiveProcess}
    (E : Expert DP) (h : ¬ Observable DP E) : ¬ LUVTotalTrustAvg P DP E :=
  fun hl => h hl.1

/-- **OPEN (trust-lab-2-006, LI non-transitivity).** Three inductors `H, A, B` (over their own
processes), a deferral `f`, with `H` LUV-Total-Trusting `A` and `A` LUV-Total-Trusting `B` at the
averaged grade, but `H` not LUV-Total-Trusting `B`. By `crossTrust_of_quoted` the failure must
come from `B`'s estimates being unquotable in `H`'s process (clause (i)) or from the deadline
clause, not from the weight classes — the re-stated conjecture. **As typed, the quotability
shape suffices** (`not_luvTotalTrustAvg_of_not_observable`): a witness needs only two instances
of the unrestricted `LUVTotalTrustAvg` for distinct inductors (of which the package has none —
F-T3 gives `LUVTotalTrustAvgOn {X}`) and an unquoted `B`; the sharper form with `Observable` held
on the long link would be, by `crossTrust_of_quoted`, a statement that no deadline program
exists for some reflecting quote, and is not typed here. Not attempted: a construction needs a
language-inclusion or time-hierarchy separation between `H`'s and `A`'s processes.
Source: trust-lab-2-006 ([[legitimacy-corrigibility-ideate]] §6 Idea L6); mandate T10; audit r2
adversarial N5
Kind: OPEN
Fidelity: variant: averaged grade; the recovery condition re-stated as quotability; the typed
form admits the quotability shape
Hyps: n/a -/
theorem li_nontransitivity_open :
    ∃ (H A B : History) (DPH DPA : DeductiveProcess) (f : DeferralFunction)
      (hA : ∀ n s, 0 ≤ A n s ∧ A n s ≤ 1) (hB : ∀ n s, 0 ≤ B n s ∧ B n s ≤ 1),
      IsLogicalInductor H DPH ∧ IsLogicalInductor A DPA ∧
      LUVTotalTrustAvg H DPH ⟨A, f, hA⟩ ∧ LUVTotalTrustAvg A DPA ⟨B, f, hB⟩ ∧
      ¬ LUVTotalTrustAvg H DPH ⟨B, f, hB⟩ := by
  sorry

end

end Cleanroom.Trust.TrustMerge
