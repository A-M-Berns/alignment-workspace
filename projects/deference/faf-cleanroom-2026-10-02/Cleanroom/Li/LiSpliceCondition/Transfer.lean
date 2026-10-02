import Cleanroom.Li.LiSpliceCondition.Condition
import Cleanroom.Li.LiSpliceCondition.Translate
import Cleanroom.Li.LiSpliceCondition.Open
import LogicalInduction.Construction.Primcodable

/-!
# `li-splice-condition` · Transfer: the two horns of E7 over FAF's criterion (T3.4, T3.5)

Package `Cleanroom.Li.LiSpliceCondition` ([[li-splice-condition-mandate]]), file 6 of the layout.

* **Computable markets.** `zeroOut P ψ Φ N` and `reprice P ψ Φ r` are computable markets when `P`
  is, `Φ` is finite and each `r φ` (`φ ∈ Φ`) is computable (`computableMarket_zeroOut`,
  `computableMarket_reprice`): the quote tables are the base table with a finite list of codes
  overriding it — FAF's `Primrec` calculus on `ℚ` and a recursion over `Φ.toList`.
* **T3.4 Convention horn.** `zeroOut_isLogicalInductor`: for an inductor `P` over `DP` and a
  sentence `ψ` refuted at stage `N`, `zeroOut P ψ Φ N` is an inductor over `DP`. Proof: a trader
  exploiting `ℙ⁰` gives, through `zeroTranslate_netWorth_eq_of_plausible` (exact on every
  plausible world, every day) and `Exploits.of_boundedDifference` at `C = 0`, a trader exploiting
  `P`; it is e.c. by the OPEN `translateStreamRewriter` (`Open.lean`), on which this headline
  rests and is listed.
* **T3.5 Free horn.** `reprice_isLogicalInductor`: likewise for `ℙ^r` with `r` valued in `[0,1]`,
  computable and e.c. on `Φ`; the bound is `repriceBound … N`. The conditional identity
  `conditionedHistory_reprice`: `ℙ^r_n(φ | ψ) = r φ n` whenever `0 < P n ψ` and `r φ n < 1` —
  **the positivity is a hypothesis** (OPEN whether any inductor satisfies it from some day on,
  `exists_inductor_pos_on_refuted`), so what is proved unconditionally is the day-wise dichotomy
  (`Condition.lean`) and, on days with a positive price, freedom.
-/

namespace Cleanroom.Li.LiSpliceCondition

open LogicalInduction LO.Propositional

/-! ## Membership in a fixed finite list of codes, primitively -/

/-- Boolean membership in a list of naturals (structural, so that its `Primrec` proof is an
induction over the fixed list).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def inList : List ℕ → ℕ → Bool
  | [], _ => false
  | c :: l, x => (c == x) || inList l x

/-- `inList` decides membership.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma inList_iff (l : List ℕ) (x : ℕ) : inList l x = true ↔ x ∈ l := by
  induction l with
  | nil => simp [inList]
  | cons c l ih =>
      simp only [inList, Bool.or_eq_true, beq_iff_eq, ih, List.mem_cons]
      constructor
      · rintro (rfl | h)
        · exact Or.inl rfl
        · exact Or.inr h
      · rintro (rfl | h)
        · exact Or.inl rfl
        · exact Or.inr h

/-- Membership in a fixed list is primitive recursive.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma inList_prim (l : List ℕ) : Primrec (inList l) := by
  induction l with
  | nil => exact Primrec.const false
  | cons c l ih =>
      have h : Primrec fun x : ℕ => ((c == x) || inList l x) :=
        Primrec.cond (PrimrecRel.comp Primrec.eq (Primrec.const c) Primrec.id).decide
          (Primrec.const true) ih
      refine h.of_eq fun x => ?_
      by_cases hc : c = x
      · subst hc; simp [inList]
      · simp [inList]

/-- The codes of the sentences dropped by `zeroOut`: `⌜ψ⌝` and `⌜φ ⋏ ψ⌝` for `φ ∈ Φ`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def zeroCodes (ψ : Sentence) (Φ : Finset Sentence) : List ℕ :=
  Encodable.encode ψ :: Φ.toList.map (fun φ => Encodable.encode (φ ⋏ ψ))

/-- A code is in `zeroCodes` iff its sentence is `ψ` or a `φ ⋏ ψ` with `φ ∈ Φ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_zeroCodes_iff (ψ : Sentence) (Φ : Finset Sentence) (χ : Sentence) :
    Encodable.encode χ ∈ zeroCodes ψ Φ ↔ (χ = ψ ∨ (condLeg ψ Φ χ).isSome) := by
  simp only [zeroCodes, List.mem_cons, List.mem_map, Finset.mem_toList, Option.isSome_iff_exists]
  constructor
  · rintro (h | ⟨φ, hφ, h⟩)
    · exact Or.inl (Encodable.encode_injective h)
    · exact Or.inr ⟨φ, condLeg_eq_some_iff.mpr ⟨(Encodable.encode_injective h).symm, hφ⟩⟩
  · rintro (rfl | ⟨φ, h⟩)
    · exact Or.inl rfl
    · obtain ⟨rfl, hφ⟩ := condLeg_eq_some_iff.mp h
      exact Or.inr ⟨φ, hφ, rfl⟩

/-- **`zeroOut` of a computable market is a computable market** (`Φ` finite).
Source: mandate T3.4 ("`ComputableMarket (zeroOut …)` needs `Φ` decidable … restrict to a finite `Finset Sentence` — say which": finite)
Kind: C
Fidelity: variant: `Φ` finite
Hyps: (a) -/
theorem computableMarket_zeroOut (P : History) (hP : ComputableMarket P) (ψ : Sentence)
    (Φ : Finset Sentence) (N : ℕ) : ComputableMarket (zeroOut P ψ Φ N) := by
  obtain ⟨M⟩ := hP.nonemptyComputation
  refine ComputableMarket.ofComputableTable
    (fun n c => if N ≤ n ∧ inList (zeroCodes ψ Φ) c = true then 0 else M.quote n c) ?_ ?_ ?_
  · intro n φ
    unfold zeroOut
    split_ifs
    · norm_num
    · exact M.price_mem_Icc n φ
  · intro n φ
    unfold zeroOut
    have hiff : (N ≤ n ∧ (φ = ψ ∨ (condLeg ψ Φ φ).isSome)) ↔
        (N ≤ n ∧ inList (zeroCodes ψ Φ) (Encodable.encode φ) = true) := by
      rw [inList_iff, mem_zeroCodes_iff]
    by_cases h : N ≤ n ∧ (φ = ψ ∨ (condLeg ψ Φ φ).isSome)
    · rw [if_pos h, if_pos (hiff.mp h)]; simp
    · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h')), M.quote_exact]
  · apply Computable.encode.comp
    have hfst : Computable fun z : ℕ => z.unpair.1 := (Primrec.fst.comp Primrec.unpair).to_comp
    have htest : Primrec fun z : ℕ =>
        decide (N ≤ z.unpair.1 ∧ inList (zeroCodes ψ Φ) z.unpair.2 = true) :=
      ((PrimrecRel.comp Primrec.nat_le (Primrec.const N) (Primrec.fst.comp Primrec.unpair)).and
        (PrimrecRel.comp Primrec.eq ((inList_prim _).comp (Primrec.snd.comp Primrec.unpair))
          (Primrec.const true))).decide
    have h := Computable.cond htest.to_comp (Computable.const (0 : ℚ))
      (marketComputation_quote_computable M)
    refine h.of_eq fun z => ?_
    simp only [Bool.cond_decide]

/-- The re-pricing quote table over a list of re-priced sentences: the first `φ` in the list with
`c = ⌜φ ⋏ ψ⌝` gives `r φ n · quote n ⌜ψ⌝`; otherwise the base quote.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def repriceQuote {P : History} (M : MarketComputation P) (ψ : Sentence)
    (r : Sentence → ℕ → ℚ) : List Sentence → ℕ → ℕ → ℚ
  | [], n, c => M.quote n c
  | φ :: l, n, c =>
      if c = Encodable.encode (φ ⋏ ψ) then r φ n * M.quote n (Encodable.encode ψ)
      else repriceQuote M ψ r l n c

/-- The re-pricing quote table is exact: over a list `l ⊆ Φ`, it is `reprice` on the sentences
re-priced through `l` and `P` elsewhere.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma repriceQuote_spec {P : History} (M : MarketComputation P) (ψ : Sentence)
    (Φ : Finset Sentence) (r : Sentence → ℕ → ℚ) (l : List Sentence) (hl : ∀ φ ∈ l, φ ∈ Φ)
    (n : ℕ) (χ : Sentence) :
    (repriceQuote M ψ r l n (Encodable.encode χ) : ℝ) =
      if (∃ φ ∈ l, χ = φ ⋏ ψ) then reprice P ψ Φ r n χ else P n χ := by
  induction l with
  | nil => simp [repriceQuote, M.quote_exact]
  | cons φ l ih =>
      simp only [repriceQuote]
      by_cases h : Encodable.encode χ = Encodable.encode (φ ⋏ ψ)
      · have hχ : χ = φ ⋏ ψ := Encodable.encode_injective h
        rw [if_pos h, if_pos ⟨φ, List.mem_cons_self .., hχ⟩, hχ,
          reprice_and P ψ Φ r n (hl φ (List.mem_cons_self ..))]
        push_cast
        rw [M.quote_exact n ψ]
      · rw [if_neg h, ih (fun φ' hφ' => hl φ' (List.mem_cons_of_mem φ hφ'))]
        have hne : ¬ χ = φ ⋏ ψ := fun h' => h (by rw [h'])
        by_cases hex : ∃ φ' ∈ l, χ = φ' ⋏ ψ
        · rw [if_pos hex, if_pos (by obtain ⟨φ', h1, h2⟩ := hex; exact ⟨φ', List.mem_cons_of_mem φ h1, h2⟩)]
        · rw [if_neg hex, if_neg]
          rintro ⟨φ', h1, h2⟩
          rcases List.mem_cons.mp h1 with rfl | h1
          · exact hne h2
          · exact hex ⟨φ', h1, h2⟩

/-- The re-pricing quote table over a fixed list is computable when each `r φ` is.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma repriceQuote_computable {P : History} (M : MarketComputation P) (ψ : Sentence)
    (r : Sentence → ℕ → ℚ) (l : List Sentence) (hr : ∀ φ ∈ l, Computable (r φ)) :
    Computable fun z : ℕ => repriceQuote M ψ r l z.unpair.1 z.unpair.2 := by
  induction l with
  | nil => exact marketComputation_quote_computable M
  | cons φ l ih =>
      have hfst : Computable fun z : ℕ => z.unpair.1 := (Primrec.fst.comp Primrec.unpair).to_comp
      have hsnd : Computable fun z : ℕ => z.unpair.2 := (Primrec.snd.comp Primrec.unpair).to_comp
      have htest : Computable fun z : ℕ => decide (z.unpair.2 = Encodable.encode (φ ⋏ ψ)) :=
        (PrimrecRel.comp Primrec.eq (Primrec.snd.comp Primrec.unpair) (Primrec.const _)).decide.to_comp
      have hrφ : Computable fun z : ℕ => r φ z.unpair.1 :=
        (hr φ (List.mem_cons_self ..)).comp hfst
      have hqψ : Computable fun z : ℕ => M.quote z.unpair.1 (Encodable.encode ψ) := by
        have := marketComputation_quote_computable M
        have hpair : Computable fun z : ℕ => Nat.pair z.unpair.1 (Encodable.encode ψ) :=
          Primrec₂.natPair.to_comp.comp hfst (Computable.const _)
        exact (this.comp hpair).of_eq fun z => by simp
      have hmul : Computable fun z : ℕ => r φ z.unpair.1 * M.quote z.unpair.1 (Encodable.encode ψ) :=
        ratMul_prim.to_comp.comp hrφ hqψ
      have h := Computable.cond htest hmul (ih fun φ' hφ' => hr φ' (List.mem_cons_of_mem φ hφ'))
      refine h.of_eq fun z => ?_
      simp only [repriceQuote, Bool.cond_decide]

/-- **`reprice` of a computable market is a computable market** (`Φ` finite, each `r φ` computable
with values in `[0,1]`).
Source: mandate T3.5 ("`ℙ^r` is computable because `ℙ` and `r` are")
Kind: C
Fidelity: variant: `Φ` finite
Hyps: (a) -/
theorem computableMarket_reprice (P : History) (hP : ComputableMarket P) (ψ : Sentence)
    (Φ : Finset Sentence) (r : Sentence → ℕ → ℚ) (hr0 : ∀ φ ∈ Φ, ∀ n, 0 ≤ r φ n)
    (hr1 : ∀ φ ∈ Φ, ∀ n, r φ n ≤ 1) (hrc : ∀ φ ∈ Φ, Computable (r φ)) :
    ComputableMarket (reprice P ψ Φ r) := by
  obtain ⟨M⟩ := hP.nonemptyComputation
  refine ComputableMarket.ofComputableTable (fun n c => repriceQuote M ψ r Φ.toList n c) ?_ ?_ ?_
  · intro n χ
    unfold reprice
    cases h : condLeg ψ Φ χ with
    | none => exact M.price_mem_Icc n χ
    | some φ =>
        obtain ⟨-, hφ⟩ := condLeg_eq_some_iff.mp h
        have h0 : (0 : ℝ) ≤ r φ n := by exact_mod_cast hr0 φ hφ n
        have h1 : (r φ n : ℝ) ≤ 1 := by exact_mod_cast hr1 φ hφ n
        have := M.price_mem_Icc n ψ
        constructor
        · exact mul_nonneg h0 this.1
        · exact mul_le_one₀ h1 this.1 this.2
  · intro n χ
    rw [repriceQuote_spec M ψ Φ r Φ.toList (fun φ hφ => Finset.mem_toList.mp hφ) n χ]
    by_cases hex : ∃ φ ∈ Φ.toList, χ = φ ⋏ ψ
    · rw [if_pos hex]
    · rw [if_neg hex]
      refine reprice_of_none P ψ Φ r n ?_
      cases h : condLeg ψ Φ χ with
      | none => rfl
      | some φ =>
          obtain ⟨hχ, hφ⟩ := condLeg_eq_some_iff.mp h
          exact absurd ⟨φ, Finset.mem_toList.mpr hφ, hχ⟩ hex
  · exact Computable.encode.comp
      (repriceQuote_computable M ψ r Φ.toList fun φ hφ => hrc φ (Finset.mem_toList.mp hφ))

/-! ## T3.4 The convention horn -/

/-- **T3.4, the convention horn.** For an inductor `P` over `DP` and a sentence `ψ` refuted at
stage `N`, the market `zeroOut P ψ Φ N` — `P` with `ψ` and every `φ ⋏ ψ` (`φ ∈ Φ`) priced `0` from
day `N` on — is a logical inductor over `DP`. On it every conditional quote on `ψ` is the cap `1`
from day `N` on (`Condition.lean`). **Rests on the OPEN certificate `translateStreamRewriter`**
(`Open.lean`): the economic step is exact (`zeroTranslate_netWorth_eq_of_plausible`, bound `0`),
the computability of the market is discharged (`computableMarket_zeroOut`); what is open is that
the zeroed trader is efficiently computable for *every* e.c. trader — a statement about `FP`
words, not a hypothesis on the trader (the mandate's wrong-quantifier hazard).
Source: [[corr-legit-neg-inventory]] 060 (E7 (i), "the market `ℙ⁰` … is a logical inductor over `D`")
Kind: C
Fidelity: variant: `Φ` finite; rests on the OPEN rewriter
Hyps: (a) throughout; the certificate is the listed OPEN fact -/
theorem zeroOut_isLogicalInductor (P : History) (DP : DeductiveProcess)
    [hLI : IsLogicalInductor P DP] (ψ : Sentence) (N : ℕ)
    (href : ∀ v : PCWorld, v.ConsistentWith (DP.D N) → ¬ v.Holds ψ) (Φ : Finset Sentence) :
    IsLogicalInductor (zeroOut P ψ Φ N) DP where
  marketComputable := computableMarket_zeroOut P hLI.marketComputable ψ Φ N
  processComputable := hLI.processComputable
  noExploit T hT hex :=
    hLI.noExploit _ (EfficientlyComputable.zeroTranslate (translateStreamRewriter ψ Φ N).1 hT)
      (hex.of_boundedDifference 0 fun n v hv => by
        rw [zeroTranslate_netWorth_eq_of_plausible DP ψ Φ N href P T n v hv, sub_self, abs_zero])

/-- On `zeroOut P ψ Φ N` every conditional quote on `ψ` is the cap `1` from day `N` on, for every
`φ` (prices nonnegative).
Source: [[corr-legit-neg-inventory]] 060 ("On it `ℙ⁰_n(φ | ψ) = 1` for every `φ`")
Kind: L
Fidelity: exact -/
theorem conditionedHistory_zeroOut (P : History) (hP : ∀ n χ, 0 ≤ P n χ) (ψ : Sentence)
    (Φ : Finset Sentence) (N : ℕ) {n : ℕ} (hn : N ≤ n) (φ : Sentence) :
    conditionedHistory (zeroOut P ψ Φ N) (fun _ => ψ) n φ = 1 := by
  unfold conditionedHistory
  refine conditionalQuote_eq_one_of_zero _ φ ψ ?_ ?_
  · unfold zeroOut; split_ifs
    · exact le_rfl
    · exact hP n _
  · unfold zeroOut; rw [if_pos ⟨hn, Or.inl rfl⟩]

/-! ## T3.5 The free horn -/

/-- **T3.5, the free horn.** For an inductor `P` over `DP`, a sentence `ψ` refuted at stage `N`,
and `r` on `Φ` valued in `[0,1]`, computable and e.c. (FAF's `MachineRatCodes`), the market
`reprice P ψ Φ r` is a logical inductor over `DP`. **Rests on the OPEN certificate
`translateStreamRewriter`**: the economic step is `repriceTranslate_netWorth_sub_le_of_plausible`
(exact from day `N`, the explicit bound `repriceBound … N` before) through
`Exploits.of_boundedDifference`; the market's computability is `computableMarket_reprice`. No
positivity of `P n ψ` is needed for inductor-hood — only for the conditional identity
(`conditionedHistory_reprice`).
Source: [[corr-legit-neg-inventory]] 061 (E7 (ii), "the market `ℙ^r` … is a logical inductor over `D`")
Kind: C
Fidelity: variant: `Φ` finite; rests on the OPEN rewriter
Hyps: (a) throughout; `hrm` is E7's "efficiently computable `r`"; the certificate is the listed OPEN fact -/
theorem reprice_isLogicalInductor (P : History) (DP : DeductiveProcess)
    [hLI : IsLogicalInductor P DP] (ψ : Sentence) (N : ℕ)
    (href : ∀ v : PCWorld, v.ConsistentWith (DP.D N) → ¬ v.Holds ψ) (Φ : Finset Sentence)
    (r : Sentence → ℕ → ℚ) (hr0 : ∀ φ ∈ Φ, ∀ n, 0 ≤ r φ n) (hr1 : ∀ φ ∈ Φ, ∀ n, r φ n ≤ 1)
    (hrc : ∀ φ ∈ Φ, Computable (r φ)) (hrm : ∀ φ ∈ Φ, MachineRatCodes (r φ)) :
    IsLogicalInductor (reprice P ψ Φ r) DP where
  marketComputable := computableMarket_reprice P hLI.marketComputable ψ Φ r hr0 hr1 hrc
  processComputable := hLI.processComputable
  noExploit T hT hex :=
    hLI.noExploit _
      (EfficientlyComputable.repriceTranslate ((translateStreamRewriter ψ Φ N).2 r hrm) hT)
      (hex.of_boundedDifference (repriceBound ψ Φ r P T N) fun n v hv =>
        repriceTranslate_netWorth_sub_le_of_plausible DP ψ Φ N href r hr0 P T n v hv)

/-- `ψ` is never a re-priced sentence (a conjunction is not its own right conjunct).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma condLeg_self (ψ : Sentence) (Φ : Finset Sentence) : condLeg ψ Φ ψ = none := by
  cases h : condLeg ψ Φ ψ with
  | none => rfl
  | some φ =>
      obtain ⟨hψ, -⟩ := condLeg_eq_some_iff.mp h
      exact absurd hψ.symm (and_ne_right φ ψ)

/-- **The conditional identity of the free horn**: on `reprice P ψ Φ r`, for `φ ∈ Φ`, a day with
`0 < P n ψ` and `r φ n < 1`, the conditional quote is exactly `r φ n`. The positivity is a
hypothesis; its inhabitation by an inductor on a refuted `ψ` is OPEN (`exists_inductor_pos_on_refuted`).
Source: [[corr-legit-neg-inventory]] 061 ("`ℙ^r_n(φ | ψ) = r(φ,n)` whenever `r(φ,n) < 1`")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem conditionedHistory_reprice (P : History) (ψ : Sentence) (Φ : Finset Sentence)
    (r : Sentence → ℕ → ℚ) (n : ℕ) {φ : Sentence} (hφ : φ ∈ Φ) (hpos : 0 < P n ψ)
    (hlt : (r φ n : ℝ) < 1) :
    conditionedHistory (reprice P ψ Φ r) (fun _ => ψ) n φ = r φ n := by
  unfold conditionedHistory
  have hψ : reprice P ψ Φ r n ψ = P n ψ := reprice_of_none P ψ Φ r n (condLeg_self ψ Φ)
  have hand : reprice P ψ Φ r n (φ ⋏ ψ) = (r φ n : ℝ) * P n ψ := reprice_and P ψ Φ r n hφ
  rw [conditionalQuote_eq_div (by rw [hand, hψ]; nlinarith), hand, hψ]
  field_simp

/-- **The free horn at the expectation**: for a LUV whose day-`n` thresholds are all in `Φ`, a
positive price of `ψ` and `r < 1` on them, the conditional expectation is the grid average of
`r` — any e.c. target in `[0,1]` up to the grid, or an incoherent pair.
Source: [[corr-legit-neg-inventory]] 061 ("`𝔼^{ℙ^r}_n(X | ψ)` can be made to converge to any efficiently computable target in `[0,1]`, or to be incoherent")
Kind: L
Fidelity: exact (at a day; the limit statement is the day-wise statement along days with a positive price) -/
theorem condExpect_reprice (P : History) (ψ : Sentence) (Φ : Finset Sentence)
    (r : Sentence → ℕ → ℚ) (X : LUV) (n : ℕ)
    (hΦ : ∀ i, i < n + 1 → X.gt ((i : ℚ) / ((n + 1 : ℕ) : ℚ)) ∈ Φ) (hpos : 0 < P n ψ)
    (hlt : ∀ i, i < n + 1 → (r (X.gt ((i : ℚ) / ((n + 1 : ℕ) : ℚ))) n : ℝ) < 1) :
    condExpect (reprice P ψ Φ r) ψ X n =
      ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ i ∈ Finset.range (n + 1), (r (X.gt ((i : ℚ) / ((n + 1 : ℕ) : ℚ))) n : ℝ) := by
  unfold condExpect LUV.expect LUV.expectApprox
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  exact conditionedHistory_reprice P ψ Φ r n (hΦ i hi') hpos (hlt i hi')

end Cleanroom.Li.LiSpliceCondition
