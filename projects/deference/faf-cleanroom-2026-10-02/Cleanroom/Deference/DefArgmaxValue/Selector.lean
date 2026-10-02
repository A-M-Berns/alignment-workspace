import Cleanroom.Found.DefLattice.Menu
import LogicalInduction.Construction.Quotation.MarketQuoteCodes
import LogicalInduction.Construction.Paper.Market

/-!
# `def-argmax-value` · Selector: the `k+1`-ary Kleene selector

The template every self-referential menu of this package is built from (mandate targets 1 and
3). FAF's `diagonalPriceDecisionPart`/`diagonalPriceDecisionCode`
(`Construction/Quotation/Packages.lean`) is a selector program whose behaviour at its own code
is "run the market on the public atom I select, output the decision `price < p`". Here the
decision is generalized from one atom at a fixed threshold to **a least-index argmax over a
computable list of quotes** that may mention the selector's own atoms:

* `argmaxList l` — the least index of a maximal entry of a list of rationals (a `findIdx` over
  a `foldl max`), primitive recursive, and characterized against `def-lattice`'s
  `Menu.argmax` by `Menu.argmax_eq_iff` / `argmax_eq_argmaxList`;
* `selectorCode quotes rel hq hrel` — Kleene's `fixed_point₂` of the program
  `c ↦ (z ↦ if rel (argmaxList (quotes c z.unpair.1)) z.unpair.2 then 1 else 0)`, for any
  `Computable₂ quotes : Code → ℕ → List ℚ` and any primitive-recursive `rel : ℕ → ℕ → Bool`;
* `selectorQuoteCode T …` — FAF's `BooleanQuoteCode` of the fixed point, so that the public
  atoms `selectorAtom T … n j := quoteAtom ⟨code, ⟨n, j⟩⟩` are e.c. (`selectorAtom_codes`) and
  **reflected** in every `paperDP T`-consistent world (`selectorAtom_holds_iff`):
  `v.Holds (a_{n,j}) ↔ rel (argmaxList (quotes code n)) j`.

The instances: target 1 (`LiarProbe.lean`) takes `quotes c n := [P_{f n}(a_{n,1}), s_{f n}]` with
`rel := (· == ·)` — the atom `a_{n,1}` is the deferred liar at the menu's own comparison; target
3 (`Punishing.lean`) takes the `k+1` deferred-day prices of the atoms with `rel := (· != ·)` —
the atom `b_{n,j}` holds iff `j` is *not* selected, so that `literalIndicator b_{n,j}` is
Abram's punishing option `1 − 1[sel_n = j]` with no negation inside the market call.

Construction-facing; `[𝗣𝗔⁻ ⪯ T]`-level (`𝗥₀ ⪯ T` for the quote code), no `𝗜𝚺₁`.
-/

namespace Cleanroom.Deference.DefArgmaxValue

open LogicalInduction Filter Topology
open Cleanroom.Found.DefLattice
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

noncomputable section

/-! ## The least-index argmax of a list -/

/-- **The least-index argmax** of a list of rationals: the first index whose entry is at least
the running `foldl max 0` (the maximum, for lists of nonnegative rationals).
Source: none: infrastructure (the computable form of `def-lattice`'s `Menu.argmax`)
Kind: D
Fidelity: n/a -/
def argmaxList (l : List ℚ) : ℕ := l.findIdx (fun x => decide (l.foldl max 0 ≤ x))

/-- `foldl max` dominates its seed and every entry.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem foldl_max_bounds : ∀ (l : List ℚ) (a : ℚ),
    a ≤ l.foldl max a ∧ ∀ x ∈ l, x ≤ l.foldl max a
  | [], a => ⟨le_rfl, fun x hx => by simp at hx⟩
  | x :: l, a => by
    simp only [List.foldl_cons, List.mem_cons]
    obtain ⟨h1, h2⟩ := foldl_max_bounds l (max a x)
    exact ⟨le_trans (le_max_left a x) h1, fun y hy => by
      rcases hy with rfl | hy
      · exact le_trans (le_max_right a y) h1
      · exact h2 y hy⟩

/-- `foldl max` is the seed or an entry.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem foldl_max_mem : ∀ (l : List ℚ) (a : ℚ), l.foldl max a = a ∨ l.foldl max a ∈ l
  | [], _ => Or.inl rfl
  | x :: l, a => by
    simp only [List.foldl_cons, List.mem_cons]
    rcases foldl_max_mem l (max a x) with h | h
    · rw [h]
      rcases le_total a x with hax | hxa
      · exact Or.inr (Or.inl (max_eq_right hax))
      · exact Or.inl (max_eq_left hxa)
    · exact Or.inr (Or.inr h)

/-- `argmaxList` is primitive recursive (`Primrec.list_foldl` with FAF's `ratMax_prim`, then
`Primrec.list_findIdx` with `ratLE_prim`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem argmaxList_primrec : Primrec argmaxList := by
  have hfold : Primrec fun l : List ℚ => l.foldl max 0 :=
    (Primrec.list_foldl Primrec.id (Primrec.const 0)
      (ratMax_prim.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂).of_eq
      (fun l => rfl)
  have hp : Primrec fun p : List ℚ × ℚ => decide (p.1.foldl max 0 ≤ p.2) :=
    ((ratLE_prim.comp (hfold.comp Primrec.fst) Primrec.snd).decide).of_eq fun p => by rfl
  exact (Primrec.list_findIdx Primrec.id hp.to₂).of_eq (fun l => rfl)

/-- **The characterization of `argmaxList` on a nonnegative finite family**: it is `j` iff `q j`
dominates every entry and strictly dominates every earlier entry.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem argmaxList_ofFn_eq_iff {k : ℕ} (q : Fin (k + 1) → ℚ) (hq : ∀ i, 0 ≤ q i)
    (j : Fin (k + 1)) :
    argmaxList (List.ofFn q) = (j : ℕ) ↔ (∀ i, q i ≤ q j) ∧ ∀ i < j, q i < q j := by
  have hge : ∀ i, q i ≤ (List.ofFn q).foldl max 0 := fun i =>
    (foldl_max_bounds (List.ofFn q) 0).2 (q i) (List.mem_ofFn.2 ⟨i, rfl⟩)
  have hmem : ∃ i, q i = (List.ofFn q).foldl max 0 := by
    rcases foldl_max_mem (List.ofFn q) 0 with h | h
    · refine ⟨0, le_antisymm (hge 0) ?_⟩
      rw [h]; exact hq 0
    · exact List.mem_ofFn.1 h
  have hlen : (j : ℕ) < (List.ofFn q).length := by rw [List.length_ofFn]; exact j.2
  unfold argmaxList
  rw [List.findIdx_eq hlen]
  simp only [List.getElem_ofFn, Fin.eta, decide_eq_true_eq, decide_eq_false_iff_not, not_le]
  constructor
  · rintro ⟨hj, hlt⟩
    refine ⟨fun i => (hge i).trans hj, fun i hi => ?_⟩
    have := hlt i hi
    simp only [Fin.eta] at this
    exact lt_of_lt_of_le this hj
  · rintro ⟨hdom, hlt⟩
    obtain ⟨i₀, hi₀⟩ := hmem
    refine ⟨hi₀ ▸ hdom i₀, fun i hi => ?_⟩
    have h1 := hlt ⟨i, lt_trans hi j.2⟩ hi
    exact lt_of_lt_of_le h1 (hge j)

/-! ## The bridge to `def-lattice`'s `Menu.argmax` -/

/-- **`Menu.argmax` is the least index dominating every quote**: `j*(n) = j` iff `m^j_n` is at
least every `m^i_n` and strictly above every `m^i_n` with `i < j`.
Source: none: infrastructure (`def-lattice` `Menu.argmax`, "the least index attaining the max")
Kind: L
Fidelity: n/a -/
theorem Menu.argmax_eq_iff {k : ℕ} {DP : DeductiveProcess} (E : Expert DP) (M : Menu k) (n : ℕ)
    (j : Fin (k + 1)) :
    M.argmax E n = j ↔
      (∀ i, M.quote E i n ≤ M.quote E j n) ∧ ∀ i < j, M.quote E i n < M.quote E j n := by
  constructor
  · intro h
    have hj : M.quote E j n = M.maxQuote E n := h ▸ M.argmax_attains E n
    refine ⟨fun i => hj ▸ M.quote_le_maxQuote E i n, fun i hi => ?_⟩
    rcases lt_or_eq_of_le (M.quote_le_maxQuote E i n) with hlt | heq
    · rw [hj]; exact hlt
    · exact absurd (h ▸ M.argmax_le E n i heq) (not_le.2 hi)
  · rintro ⟨hdom, hlt⟩
    have hj : M.quote E j n = M.maxQuote E n := by
      apply le_antisymm (M.quote_le_maxQuote E j n)
      unfold Menu.maxQuote
      exact Finset.sup'_le _ _ (fun i _ => hdom i)
    have hle : M.argmax E n ≤ j := M.argmax_le E n j hj
    rcases lt_or_eq_of_le hle with h | h
    · have h1 := hlt _ h
      rw [M.argmax_attains E n, ← hj] at h1
      exact absurd h1 (lt_irrefl _)
    · exact h

/-- **The argmax of a menu is `argmaxList` of its rational quotes**: for any rational family
`q` casting to the quotes, `(M.argmax E n : ℕ) = argmaxList (List.ofFn q)`.
Source: none: infrastructure (the computable rendering of the ledger-decided tie-break)
Kind: L
Fidelity: n/a -/
theorem argmax_eq_argmaxList {k : ℕ} {DP : DeductiveProcess} (E : Expert DP) (M : Menu k)
    (n : ℕ) (q : Fin (k + 1) → ℚ) (hq : ∀ i, ((q i : ℚ) : ℝ) = M.quote E i n) :
    (M.argmax E n : ℕ) = argmaxList (List.ofFn q) := by
  have hq0 : ∀ i, 0 ≤ q i := fun i => by
    have := (E.estimate_mem_Icc (M.O i) n).1
    have h' : ((q i : ℚ) : ℝ) = E.estimate (M.O i) n := hq i
    rw [← h'] at this
    exact_mod_cast this
  symm
  rw [argmaxList_ofFn_eq_iff q hq0 (M.argmax E n)]
  have h := (Menu.argmax_eq_iff E M n (M.argmax E n)).1 rfl
  refine ⟨fun i => ?_, fun i hi => ?_⟩
  · have := h.1 i
    rw [← hq i, ← hq (M.argmax E n)] at this
    exact_mod_cast this
  · have := h.2 i hi
    rw [← hq i, ← hq (M.argmax E n)] at this
    exact_mod_cast this

/-- The converse direction: if `argmaxList` of the rational quotes is `j`, the menu's argmax is `j`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem argmax_eq_of_argmaxList {k : ℕ} {DP : DeductiveProcess} (E : Expert DP) (M : Menu k)
    (n : ℕ) (q : Fin (k + 1) → ℚ) (hq : ∀ i, ((q i : ℚ) : ℝ) = M.quote E i n) (j : Fin (k + 1)) :
    M.argmax E n = j ↔ argmaxList (List.ofFn q) = (j : ℕ) := by
  rw [← argmax_eq_argmaxList E M n q hq]
  exact ⟨fun h => by rw [h], fun h => Fin.ext h⟩

/-! ## The Kleene selector -/

section Selector

variable (quotes : Nat.Partrec.Code → ℕ → List ℚ) (rel : ℕ → ℕ → Bool)

/-- **The selector program**, as a function of a candidate code `c`: on input `⟨n, j⟩`, output
`1` iff `rel (argmaxList (quotes c n)) j`. Kleene's second recursion theorem chooses a code
whose behaviour is this very computation at its own code (`selectorCode`).
Source: FAF `diagonalPriceDecisionPart` (`thm:lp`), generalized from one atom at a fixed
threshold to a list of quotes and a least-index argmax
Kind: D
Fidelity: exact -/
def selectorPart (c : Nat.Partrec.Code) (z : ℕ) : Part ℕ :=
  Part.some (if rel (argmaxList (quotes c z.unpair.1)) z.unpair.2 then 1 else 0)

/-- The selector program is partial recursive in `(c, z)` (total, in fact).
Source: FAF `diagonalPriceDecisionPart_partrec`
Kind: L
Fidelity: n/a -/
theorem selectorPart_partrec (hq : Computable₂ quotes) (hrel : Primrec₂ rel) :
    Partrec₂ (selectorPart quotes rel) := by
  have h1 : Computable fun p : Nat.Partrec.Code × ℕ => quotes p.1 p.2.unpair.1 :=
    hq.comp Computable.fst (Computable.fst.comp (Computable.unpair.comp Computable.snd))
  have h2 : Computable fun p : Nat.Partrec.Code × ℕ =>
      rel (argmaxList (quotes p.1 p.2.unpair.1)) p.2.unpair.2 :=
    hrel.to_comp.comp (argmaxList_primrec.to_comp.comp h1)
      (Computable.snd.comp (Computable.unpair.comp Computable.snd))
  have h3 : Computable fun p : Nat.Partrec.Code × ℕ =>
      (if rel (argmaxList (quotes p.1 p.2.unpair.1)) p.2.unpair.2 then 1 else 0 : ℕ) :=
    (Computable.cond h2 (Computable.const 1) (Computable.const 0)).of_eq
      (fun p => by simp [Bool.cond_eq_ite])
  exact h3.partrec.of_eq (fun p => rfl)

/-- **The Kleene fixed point**: the selector code whose evaluation is `selectorPart` at itself.
Source: FAF `diagonalPriceDecisionCode` (`Nat.Partrec.Code.fixed_point₂`)
Kind: D
Fidelity: exact -/
def selectorCode (hq : Computable₂ quotes) (hrel : Primrec₂ rel) : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.fixed_point₂ (selectorPart_partrec quotes rel hq hrel))

/-- The fixed-point equation.
Source: FAF `diagonalPriceDecisionCode_spec`
Kind: L
Fidelity: n/a -/
theorem selectorCode_spec (hq : Computable₂ quotes) (hrel : Primrec₂ rel) :
    (selectorCode quotes rel hq hrel).eval = selectorPart quotes rel (selectorCode quotes rel hq hrel) :=
  Classical.choose_spec (Nat.Partrec.Code.fixed_point₂ (selectorPart_partrec quotes rel hq hrel))

/-- **The decision the fixed selector makes at `⟨n, j⟩`**: `rel (argmaxList (quotes code n)) j`,
with `code` the selector itself — the semantic predicate the public atoms quote.
Source: FAF `diagonalPriceTruth`
Kind: D
Fidelity: exact -/
def selectorTruth (hq : Computable₂ quotes) (hrel : Primrec₂ rel) (z : ℕ) : Prop :=
  rel (argmaxList (quotes (selectorCode quotes rel hq hrel) z.unpair.1)) z.unpair.2 = true

/-- The fixed selector evaluates to the decision at its own code.
Source: FAF `diagonalPriceDecisionCode_eval`
Kind: L
Fidelity: n/a -/
theorem selectorCode_eval (hq : Computable₂ quotes) (hrel : Primrec₂ rel) (z : ℕ) :
    (selectorCode quotes rel hq hrel).eval z =
      Part.some (if rel (argmaxList (quotes (selectorCode quotes rel hq hrel) z.unpair.1))
        z.unpair.2 then 1 else 0) := by
  rw [selectorCode_spec]
  rfl

/-- The positive quotation fiber of the selector is its decision.
Source: FAF `diagonalPriceQuotePos_iff`
Kind: L
Fidelity: n/a -/
theorem selector_quotePos_iff (hq : Computable₂ quotes) (hrel : Primrec₂ rel) (z : ℕ) :
    quotePos (Encodable.encode (selectorCode quotes rel hq hrel)) z ↔
      selectorTruth quotes rel hq hrel z := by
  classical
  rw [quotePos]
  simp only [decodedComputation, Denumerable.ofNat_encode, selectorCode_eval, selectorTruth]
  split <;> simp_all

/-- The negative quotation fiber of the selector is the complement of its decision.
Source: FAF `diagonalPriceQuoteNeg_iff`
Kind: L
Fidelity: n/a -/
theorem selector_quoteNeg_iff (hq : Computable₂ quotes) (hrel : Primrec₂ rel) (z : ℕ) :
    quoteNeg (Encodable.encode (selectorCode quotes rel hq hrel)) z ↔
      ¬ selectorTruth quotes rel hq hrel z := by
  classical
  rw [quoteNeg]
  simp only [decodedComputation, Denumerable.ofNat_encode, selectorCode_eval, selectorTruth]
  split <;> simp_all

variable (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T]

/-- **FAF's Boolean quote code of the fixed selector**: the public atoms `quoteAtom ⟨code, z⟩`
are `T`-complete for the decision (Σ₁-completeness, `universalQuotePos_prov`/`Neg_prov`),
exactly as `parameterizedDiagonalQuoteCodeOfMarket` packages FAF's one-atom diagonal. The
FFL `body` of a `ParameterizedDiagonalQuoteCode` is not needed: reflection in completed-theory
worlds is `BooleanQuoteCode.reflected`.
Source: FAF `parameterizedDiagonalQuoteCodeOfMarket` (`thm:lp`), the `toBooleanQuoteCode` part
Kind: D
Fidelity: exact -/
def selectorQuoteCode (hq : Computable₂ quotes) (hrel : Primrec₂ rel) :
    BooleanQuoteCode T (selectorTruth quotes rel hq hrel) where
  code := Encodable.encode (selectorCode quotes rel hq hrel)
  pos_complete := fun z hz =>
    universalQuotePos_prov T <| by
      simpa [Nat.unpair_pair] using (selector_quotePos_iff quotes rel hq hrel z).mpr hz
  neg_complete := fun z hz =>
    universalQuoteNeg_prov T <| by
      simpa [Nat.unpair_pair] using (selector_quoteNeg_iff quotes rel hq hrel z).mpr hz

/-- **The public selection atom** `a_{n,j} := quoteAtom ⟨code, ⟨n, j⟩⟩`.
Source: mandate target 3a ("public atoms `a_{n,j} := quoteAtom ⟨c, ⟨n, j⟩⟩`")
Kind: D
Fidelity: exact -/
def selectorAtom (hq : Computable₂ quotes) (hrel : Primrec₂ rel) (n j : ℕ) : Sentence :=
  (selectorQuoteCode quotes rel T hq hrel).sentence (Nat.pair n j)

/-- The atoms at a fixed option index are e.c. in the day (the quote code's polynomial sentence
emitter read at `⟨n, j⟩`).
Source: none: infrastructure (FAF `BooleanQuoteCode.sentence_poly`)
Kind: L
Fidelity: n/a -/
theorem selectorAtom_codes (hq : Computable₂ quotes) (hrel : Primrec₂ rel) (j : ℕ) :
    MachineSentenceCodes (fun n => selectorAtom quotes rel T hq hrel n j) :=
  (MachineSentenceCodes.comp
    (MachineSentenceCodes.ofPolySentenceCodes (selectorQuoteCode quotes rel T hq hrel).sentence_poly)
    (UnaryRuler.id.pair (UnaryRuler.const j))).of_eq (fun _ => rfl)

/-- **The atoms are reflected**: a `paperDP T`-consistent world holds `a_{n,j}` iff
`rel (argmaxList (quotes code n)) j` — the fixed-point equation read inside every completed
theory (FAF `BooleanQuoteCode.reflected` at `paperQuotationPresentation T`).
Source: mandate target 3a, world fact (α); FAF `BooleanQuoteCode.reflected`
Kind: L
Fidelity: n/a -/
theorem selectorAtom_holds_iff (hq : Computable₂ quotes) (hrel : Primrec₂ rel) (n j : ℕ)
    (v : PCWorld) (hv : v.ConsistentWithTheory (paperDP T)) :
    v.Holds (selectorAtom quotes rel T hq hrel n j) ↔
      rel (argmaxList (quotes (selectorCode quotes rel hq hrel) n)) j = true := by
  unfold selectorAtom
  rw [BooleanQuoteCode.reflected (paperQuotationPresentation T) _ _ v hv]
  simp [selectorTruth, Nat.unpair_pair]

end Selector

end

end Cleanroom.Deference.DefArgmaxValue
