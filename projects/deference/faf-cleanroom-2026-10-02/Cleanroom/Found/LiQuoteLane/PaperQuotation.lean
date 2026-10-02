import Cleanroom.Found.LiQuoteLane.OneWay
import Cleanroom.Bli.BliFound.PaperInstances
import LogicalInduction.Construction.Paper.TheoremDP
import LogicalInduction.Construction.Quotation.MarketQuoteCodes

/-!
# `li-quote-lane` · PaperQuotation: Route Q — the ledger literal is an arithmetic fact (T1.6)

Over FAF's paper process `paperDP T` (`[T.Δ₁] [𝗥₀ ⪯ T]`), `A`'s quote table is a total computable
`[0,1]`-rational sequence (`liaQuote_computable`, `liaQuote_mem`), so FAF's
`RationalQuoteCode.ofComputable` gives it a **quote code** `aQuoteCode`: a Σ₁ quotation literal
family `quoteAtom ⟨code, ⟨⟨j, n⟩, ⌜r⌝⟩⟩` that `paperDP T` decides at `A`'s exact quote
(`RationalQuoteCode.reflected` at `paperQuotationPresentation T`) — exactly as `bli-found` built
`marketQuoteCode` for the market's own prices. The **alias theorem** `ledger_quote_alias`: in
every completed-theory world of the ledger process over `paperDP T`, the fresh ledger LUV
`α_{j,n}` and the quotation LUV `aQuoteCode.luv ⟨j, n⟩` are both valued at `liaQuote DPA n
(quoted j n)`, hence their threshold sentences agree at every `r ≠ a_{j,n}`. This is the precise
sense in which the plan's "the decided-value atoms are `RepresentsComputations` facts, not free"
holds: the fresh literal *agrees with* a Σ₁ quotation literal `paperDP T` already decides.

**Disclosures.** The alias holds only over `paperDP T` bases (Σ₁-completeness of `T` about `A`'s
program is what `ofComputable` consumes). The fresh atoms are what carry the *publication stage*
`e` (`ledgerSchedule_mem_iff`): FAF's dovetailed quotation stream reaches
`quoteAtom ⟨code, input⟩` at a stage nobody controls (`bli-found` findings F-14). At `r = a_{j,n}`
`PCWorld.ValuesAt` constrains neither side, so no claim is made there. No `Sminus` / `atomDay`
claim is made. Scope: one-way.
-/

namespace Cleanroom.Found.LiQuoteLane

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiAsympCalc

/-- `A`'s quote table as a one-index value sequence: at `z = ⟨j, n⟩`, `A`'s day-`n` price of
`quoted j n`.
Source: mandate T1.6
Kind: D
Fidelity: n/a -/
noncomputable def quoteValue (DPA : DeductiveProcess) (quoted : ℕ → ℕ → Sentence) (z : ℕ) : ℚ :=
  liaQuote DPA z.unpair.2 (quoted z.unpair.1 z.unpair.2)

/-- `quoteValue_pair`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma quoteValue_pair (DPA : DeductiveProcess) (quoted : ℕ → ℕ → Sentence) (j n : ℕ) :
    quoteValue DPA quoted (Nat.pair j n) = liaQuote DPA n (quoted j n) := by
  simp [quoteValue]

/-- The packed quote table is computable.
Source: none: infrastructure (`liaQuote_computable`)
Kind: L
Fidelity: n/a -/
lemma quoteValue_computable (DPA : DeductiveProcess) (hA : ComputableDeductiveProcess DPA)
    (quoted : ℕ → ℕ → Sentence) (hq : Computable fun p : ℕ × ℕ => quoted p.1 p.2) :
    Computable (quoteValue DPA quoted) :=
  ((liaQuote_computable DPA hA quoted hq).comp Primrec.unpair.to_comp).of_eq fun _ => rfl

/-- The packed quote table lies in `[0,1]`.
Source: none: infrastructure (`liaQuote_mem`)
Kind: L
Fidelity: n/a -/
lemma quoteValue_mem (DPA : DeductiveProcess) (quoted : ℕ → ℕ → Sentence) (z : ℕ) :
    0 ≤ quoteValue DPA quoted z ∧ quoteValue DPA quoted z ≤ 1 :=
  liaQuote_mem _ _ _

/-- A world consistent with every stage of the ledger process is consistent with every stage of
the base.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma consistentWithTheory_base_of_ledger {base : DeductiveProcess} {a : ℕ → ℕ → ℚ}
    {e : ℕ → PublicationSchedule} {v : PCWorld}
    (hv : v.ConsistentWithTheory (ledgerProcess base a e)) : v.ConsistentWithTheory base :=
  fun n φ hφ => hv n φ (Finset.mem_union_left _ hφ)

section

variable (T : LO.FirstOrder.ArithmeticTheory) [T.Δ₁] [𝗥₀ ⪯ T]

/-- **`A`'s quote code**: FAF's `RationalQuoteCode` naming `A`'s quote table, whose threshold
literals `⌜a_{j,n} > r⌝` are tag-`2` quotation atoms that `paperDP T` decides
(`RationalQuoteCode.ofComputable`, as `bli-found`'s `marketQuoteCode`).
Source: mandate T1.6; FAF `RationalQuoteCode.ofComputable`
Kind: D
Fidelity: exact -/
noncomputable def aQuoteCode (DPA : DeductiveProcess) (hA : ComputableDeductiveProcess DPA)
    (quoted : ℕ → ℕ → Sentence) (hq : Computable fun p : ℕ × ℕ => quoted p.1 p.2) :
    RationalQuoteCode T (quoteValue DPA quoted) :=
  RationalQuoteCode.ofComputable T (quoteValue_computable DPA hA quoted hq)
    (quoteValue_mem DPA quoted)

/-- Every completed-theory world of `paperDP T` values the quotation LUV `aQuoteCode.luv ⟨j, n⟩`
at `A`'s exact day-`n` quote of `quoted j n`.
Source: mandate T1.6; FAF `RationalQuoteCode.reflected` at `paperQuotationPresentation`
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem aQuoteCode_valuesAt (DPA : DeductiveProcess) (hA : ComputableDeductiveProcess DPA)
    (quoted : ℕ → ℕ → Sentence) (hq : Computable fun p : ℕ × ℕ => quoted p.1 p.2) (j n : ℕ)
    (v : PCWorld) (hv : v.ConsistentWithTheory (paperDP T)) :
    v.ValuesAt ((aQuoteCode T DPA hA quoted hq).luv (Nat.pair j n))
      (liaQuote DPA n (quoted j n) : ℝ) := by
  have := (aQuoteCode T DPA hA quoted hq).reflected (paperQuotationPresentation T)
    (Nat.pair j n) v hv
  simpa using this

/-- **T1.6, the alias theorem (Route Q).** In every completed-theory world of the ledger process
over `paperDP T` (with `A`'s quotes as the table), the fresh ledger LUV `α_{j,n}` and the Σ₁
quotation LUV `aQuoteCode.luv ⟨j, n⟩` are both valued at `liaQuote DPA n (quoted j n)`, so their
threshold sentences agree at every `r ≠ a_{j,n}`: the ledger literal is (extensionally) an
arithmetic fact `paperDP T` already decides. Left side by T1.2, right side by
`RationalQuoteCode.reflected`. Disclosures in the module docstring. Scope: one-way.
Source: mandate T1.6 (plan: "the decided-value atoms are `RepresentsComputations` facts, not free"); `bli-found` `quoteLuv_valuesAt` (the same-market pattern)
Kind: C
Fidelity: exact (agreement off the value; `ValuesAt` constrains neither side at the value)
Hyps: (a) none -/
theorem ledger_quote_alias (DPA : DeductiveProcess) (hA : ComputableDeductiveProcess DPA)
    (quoted : ℕ → ℕ → Sentence) (hq : Computable fun p : ℕ × ℕ => quoted p.1 p.2)
    (e : ℕ → PublicationSchedule) (j n : ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory
      (ledgerProcess (paperDP T) (fun j n => liaQuote DPA n (quoted j n)) e)) :
    v.ValuesAt (ledgerLuv j n) (liaQuote DPA n (quoted j n) : ℝ) ∧
    v.ValuesAt ((aQuoteCode T DPA hA quoted hq).luv (Nat.pair j n))
      (liaQuote DPA n (quoted j n) : ℝ) ∧
    ∀ r : ℚ, r ≠ liaQuote DPA n (quoted j n) →
      (v.Holds ((ledgerLuv j n).gt r) ↔
        v.Holds (((aQuoteCode T DPA hA quoted hq).luv (Nat.pair j n)).gt r)) := by
  have h1 := ledgerLuv_determinedVia (paperDP T) _ e
    (fun j n => liaQuote_mem DPA n (quoted j n)) j n v hv
  have h2 := aQuoteCode_valuesAt T DPA hA quoted hq j n v (consistentWithTheory_base_of_ledger hv)
  refine ⟨h1, h2, fun r hr => ?_⟩
  rcases lt_or_gt_of_ne hr with hlt | hgt
  · have hlt' : (r : ℝ) < (liaQuote DPA n (quoted j n) : ℝ) := by exact_mod_cast hlt
    exact ⟨fun _ => (h2.2.2 r).1 hlt', fun _ => (h1.2.2 r).1 hlt'⟩
  · have hgt' : (liaQuote DPA n (quoted j n) : ℝ) < r := by exact_mod_cast hgt
    exact ⟨fun h => absurd h ((h1.2.2 r).2 hgt'), fun h => absurd h ((h2.2.2 r).2 hgt')⟩

omit [𝗥₀ ⪯ T] in
/-- **T1.5 at a real base:** every stage of the ledger process over `paperDP T` has a consistent
world (from `paperDP_hworld` and `paperDP_cleanroomFree`), for any table and schedules.
Source: mandate T1.5; FAF `paperDP_hworld`; `bli-found` `paperDP_cleanroomFree`
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem ledgerProcess_paperDP_hworld [𝗣𝗔⁻ ⪯ T] [LO.Entailment.Consistent T] (a : ℕ → ℕ → ℚ)
    (e : ℕ → PublicationSchedule) :
    ∀ n, ∃ v : PCWorld, v.ConsistentWith ((ledgerProcess (paperDP T) a e).D n) :=
  ledgerProcess_hworld (processFreeOf_ledgerSchedule_of_cleanroomFree (paperDP_cleanroomFree T))
    (paperDP_hworld T)

end

end Cleanroom.Found.LiQuoteLane
