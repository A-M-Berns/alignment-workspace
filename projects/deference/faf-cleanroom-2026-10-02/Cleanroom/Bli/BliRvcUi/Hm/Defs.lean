import Cleanroom.Bli.BliFound.StateSentence
import LogicalInduction.Construction.Quotation.Packages
import LogicalInduction.Construction.Quotation.MarketQuoteCodes

/-!
# `bli-rvc-ui` · Hm/Defs: hypothetical marginalization as a computable function of a table's code

**Design decision 6 of the mandate.** The 2024-10 talk (p. 28) wants functions `v(Q, x)`, `p(Q, x)`
that pull values out of a written-out state `Q` and a prior that "just knows the output to these
functions": `v(Q,x) = r ⇒ ℙ₀(v(Q,x) = r) = 1`. Over FAF a written-out state is a *code* `q`
(`bli-found`'s `tableOfCode q : List (ℕ × ℕ)`), a decidable predicate of the table is a
`ComputablePred` of the code, and FAF's quotation package turns any such predicate into a
`BooleanQuoteCode`, whose literal `⌜F(q)⌝` is a tag-`2` quotation atom that `paperDP T` decides
(`quote_positive_enters` / `quote_negative_refutes`). Likewise a computable rational reading of the
table is a `RationalQuoteCode`, whose LUV every completed-theory world values at the reading.

* `hmQuote T hF`, `hmSentence T hF q` — the Boolean form `⌜F(q)⌝`.
* `hmRatQuote T hM hMmem`, `hmLuv T hM hMmem z` — the LUV form `[M](z)`.
* `HMExact V hF Q` — the prior assigns each `⌜F(q)⌝`, `q ∈ Q`, the truth value `[F q]`.
* `entryAtLeast c r` and `tableEntryValue c d` — the table predicates of record for the witnesses:
  "the entry of sentence code `c` is at least `r`" and "the entry of `c`, as a fraction of `d`,
  clamped to `[0,1]`", both computable.
* `ReflectionSoto` — bli-soto-a-088's "(b) + (c) = Reflection Principle for finite states" as the
  named conjunction `E2xσ ∧ HMExact` (**ATTRIBUTION-UNVETTED** identification; `rfl`-level only).

**No market anywhere.** `hmSentence`/`hmLuv` mention no `marketValue`, no `cellTruth`, no
`liaHistory`: `bli-found`'s `cellTruth T round z` reads the *actual* market quote and is linkage
(B2), not hypothetical marginalization. The market enters only as the *process* of the theorems
in `Hm/Paper.lean` (`paperDP T`), never in the definitions.
-/

namespace Cleanroom.Bli.BliRvcUi

open LogicalInduction LO.Propositional Finset Cleanroom.Bli.BliFound

section Quote

variable (T : LO.FirstOrder.ArithmeticTheory) [T.Δ₁] [𝗥₀ ⪯ T]

/-- **The HM quote code** of a computable predicate `F` of table codes: FAF's
`BooleanQuoteCode.ofComputable`.
Source: mandate design decision 6; bli-soto-a-014; bli-slides-033 (HM)
Kind: D
Fidelity: exact -/
noncomputable def hmQuote {F : ℕ → Prop} (hF : ComputablePred F) : BooleanQuoteCode T F :=
  BooleanQuoteCode.ofComputable hF

/-- **The HM literal** `⌜F(q)⌝`: the quotation atom naming "`F` holds of the table with code `q`".
Source: mandate design decision 6; talk 2024-10 p. 28 (`v(Q,x) = r`); bli-soto-b-040 (the `M` function)
Kind: D
Fidelity: exact (Boolean form) -/
noncomputable def hmSentence {F : ℕ → Prop} (hF : ComputablePred F) (q : ℕ) : Sentence :=
  (hmQuote T hF).sentence q

omit [T.Δ₁] in
/-- `hmSentence` is a single tag-`2` quotation atom (so it is an atom, and its atom code carries
tag `2`).
Source: FAF `BooleanQuoteCode.sentence`, `sentenceAtomCodes_quoteAtom`
Kind: L
Fidelity: n/a -/
lemma hmSentence_eq_quoteAtom {F : ℕ → Prop} (hF : ComputablePred F) (q : ℕ) :
    hmSentence T hF q = quoteAtom (Nat.pair (hmQuote T hF).code q) := rfl

/-- **The HM rational quote code** of a computable `[0,1]`-valued reading `M` of codes: FAF's
`RationalQuoteCode.ofComputable`.
Source: mandate design decision 6; bli-soto-a-014 (`[X](Q̂)` for a LUV `X`)
Kind: D
Fidelity: exact -/
noncomputable def hmRatQuote {M : ℕ → ℚ} (hM : Computable M) (hMmem : ∀ z, 0 ≤ M z ∧ M z ≤ 1) :
    RationalQuoteCode T M :=
  RationalQuoteCode.ofComputable T hM hMmem

/-- **The HM LUV** `[M](z)`: the threshold family of the rational quote code at `z`.
Source: mandate design decision 6; thread l. 1165 (Abram: "`[prop](Q)` known to within ε")
Kind: D
Fidelity: exact (LUV form) -/
noncomputable def hmLuv {M : ℕ → ℚ} (hM : Computable M) (hMmem : ∀ z, 0 ≤ M z ∧ M z ≤ 1)
    (z : ℕ) : LUV :=
  (hmRatQuote T hM hMmem).luv z

open Classical in
/-- **Exact hypothetical marginalization at one valuation** on the codes `Q`: `V ⌜F(q)⌝ = [F q]`.
Source: [[bli-program-desiderata]] D-HM ("`ℙ_n(F(T)) = [F(T)]`"); talk 2024-10 p. 28
Kind: D
Fidelity: exact -/
def HMExact (V : Sentence → ℝ) {F : ℕ → Prop} (hF : ComputablePred F) (Q : Finset ℕ) : Prop :=
  ∀ q ∈ Q, V (hmSentence T hF q) = if F q then 1 else 0

end Quote

/-! ## The table predicates of record -/

/-- The Boolean decider of "some entry of the table with code `q` has sentence code `c` and grid
index `≥ r`", as a fold over `bli-found`'s `tableOfCode`.
Source: mandate design decision 6 (`F q := ∃ e ∈ tableOfCode q, e.1 = c ∧ r ≤ e.2`)
Kind: D
Fidelity: n/a -/
def tableHasAtLeast (c r : ℕ) (q : ℕ) : Bool :=
  (tableOfCode q).foldr
    (fun e acc => if e.1 = c then (if r ≤ e.2 then true else acc) else acc) false

/-- The fold decides membership of a qualifying entry.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma foldr_hasAtLeast_iff (c r : ℕ) : ∀ l : List (ℕ × ℕ),
    (l.foldr (fun e acc => if e.1 = c then (if r ≤ e.2 then true else acc) else acc) false)
      = true ↔ ∃ e ∈ l, e.1 = c ∧ r ≤ e.2
  | [] => by simp
  | e :: l => by
      rw [List.foldr_cons]
      by_cases hc : e.1 = c
      · by_cases hr : r ≤ e.2
        · simp [hc, hr]
        · simp only [hc, if_true, hr, if_false, foldr_hasAtLeast_iff c r l, List.mem_cons]
          constructor
          · rintro ⟨e', he', h⟩
            exact ⟨e', Or.inr he', h⟩
          · rintro ⟨e', (rfl | he'), h⟩
            · exact absurd h.2 hr
            · exact ⟨e', he', h⟩
      · simp only [hc, if_false, foldr_hasAtLeast_iff c r l, List.mem_cons]
        constructor
        · rintro ⟨e', he', h⟩
          exact ⟨e', Or.inr he', h⟩
        · rintro ⟨e', (rfl | he'), h⟩
          · exact absurd h.1 hc
          · exact ⟨e', he', h⟩

/-- **The table predicate of record**: the table with code `q` lists sentence code `c` with a grid
index at least `r`. (`tableOfCode` of a non-list code is `[]`, so the predicate is false there.)
Source: mandate design decision 6
Kind: D
Fidelity: exact -/
def entryAtLeast (c r : ℕ) (q : ℕ) : Prop := ∃ e ∈ tableOfCode q, e.1 = c ∧ r ≤ e.2

/-- `tableHasAtLeast_iff`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tableHasAtLeast_iff (c r q : ℕ) : tableHasAtLeast c r q = true ↔ entryAtLeast c r q :=
  foldr_hasAtLeast_iff c r (tableOfCode q)

/-- `tableOfCode` is primitive recursive (decode, default `[]`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tableOfCode_prim : Primrec tableOfCode :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const [])

/-- The decider is primitive recursive (a fold with a primitive recursive step).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tableHasAtLeast_prim (c r : ℕ) : Primrec (tableHasAtLeast c r) := by
  unfold tableHasAtLeast
  refine Primrec.list_foldr (f := tableOfCode) (g := fun _ => false)
    (h := fun _ p => if p.1.1 = c then (if r ≤ p.1.2 then true else p.2) else p.2)
    tableOfCode_prim (Primrec.const false) ?_
  refine Primrec.ite (Primrec.eq.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
    (Primrec.const c)) ?_ (Primrec.snd.comp Primrec.snd)
  exact Primrec.ite (Primrec.nat_le.comp (Primrec.const r)
    (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))) (Primrec.const true)
    (Primrec.snd.comp Primrec.snd)

/-- **The table predicate is a `ComputablePred`** of the code — the hypothesis `hmSentence` takes.
Source: mandate design decision 6 ("a decidable predicate of a written-out table is a computation")
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem entryAtLeast_computable (c r : ℕ) : ComputablePred (entryAtLeast c r) := by
  rw [ComputablePred.computable_iff]
  refine ⟨tableHasAtLeast c r, (tableHasAtLeast_prim c r).to_comp, ?_⟩
  funext q
  exact propext (tableHasAtLeast_iff c r q).symm

/-- The entry of sentence code `c` in the table with code `q` (`0` if unlisted), as a fold.
Source: mandate design decision 6 (`(entryOf c (tableOfCode q)).getD 0`)
Kind: D
Fidelity: n/a -/
def tableEntry (c : ℕ) (q : ℕ) : ℕ :=
  (tableOfCode q).foldr (fun e acc => if e.1 = c then e.2 else acc) 0

/-- The fold agrees with `bli-found`'s `entryOf` (default `0`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma foldr_entry_eq_entryOf (c : ℕ) : ∀ l : List (ℕ × ℕ),
    l.foldr (fun e acc => if e.1 = c then e.2 else acc) 0 = (entryOf c l).getD 0
  | [] => by simp [entryOf]
  | e :: l => by
      rw [List.foldr_cons]
      by_cases hc : e.1 = c
      · simp [entryOf, hc]
      · simp [entryOf, hc, foldr_entry_eq_entryOf c l]

/-- `tableEntry_eq_entryOf`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tableEntry_eq_entryOf (c q : ℕ) : tableEntry c q = (entryOf c (tableOfCode q)).getD 0 :=
  foldr_entry_eq_entryOf c (tableOfCode q)

/-- `tableEntry_prim`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tableEntry_prim (c : ℕ) : Primrec (tableEntry c) := by
  unfold tableEntry
  refine Primrec.list_foldr (f := tableOfCode) (g := fun _ => 0)
    (h := fun _ p => if p.1.1 = c then p.1.2 else p.2) tableOfCode_prim
    (Primrec.const 0) ?_
  exact Primrec.ite (Primrec.eq.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
    (Primrec.const c)) (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
    (Primrec.snd.comp Primrec.snd)

/-- **The rational reading of record**: the entry of `c` as a fraction of the mesh `d`, clamped to
`1` when the entry exceeds `d` (so that the reading is a `[0,1]`-value for every code).
Source: mandate design decision 6 (`M ⟨q, c⟩ := entry / d`)
Kind: D
Fidelity: variant: clamped at `1` (the mandate's `entry / d` leaves `[0,1]` on illegitimate codes) -/
def tableEntryValue (c d : ℕ) (q : ℕ) : ℚ :=
  if tableEntry c q ≤ d then mkRat (tableEntry c q : ℤ) d else 1

/-- `tableEntryValue` is computable (FAF's `ratMk_prim`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tableEntryValue_computable (c d : ℕ) : Computable (tableEntryValue c d) := by
  unfold tableEntryValue
  refine Primrec.to_comp ?_
  refine Primrec.ite (Primrec.nat_le.comp (tableEntry_prim c) (Primrec.const d))
    (ratMk_prim.comp (intOfNat_prim.comp (tableEntry_prim c)) (Primrec.const d))
    (Primrec.const 1)

/-- `tableEntryValue` lies in `[0,1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tableEntryValue_mem (c d q : ℕ) : 0 ≤ tableEntryValue c d q ∧ tableEntryValue c d q ≤ 1 := by
  unfold tableEntryValue
  split_ifs with h
  · rw [Rat.mkRat_eq_div]
    rcases Nat.eq_zero_or_pos d with hd | hd
    · simp [hd]
    · have hd' : (0 : ℚ) < d := by exact_mod_cast hd
      constructor
      · exact div_nonneg (by exact_mod_cast Int.natCast_nonneg _) hd'.le
      · rw [div_le_one hd']
        exact_mod_cast h
  · exact ⟨zero_le_one, le_rfl⟩

/-! ## Soto's "Reflection Principle for finite states" -/

/-- **bli-soto-a-088 / bli-soto-b-040**: Soto's "(b) self-trust + (c) hypothetical marginalization
= the Reflection Principle for finite states", in this run's vocabulary: exact faith in the
state-sentence family `σ` (`bli-found`'s `E2xσ`) together with exact HM on the codes `Q n` at
every day. **ATTRIBUTION-UNVETTED**: that this conjunction is what Soto meant by "Reflection
Principle" is an identification by this package, not a statement of his; nothing is proved about
it beyond unfolding.
Source: bli-soto-a-088; bli-soto-b-040; thread l. 954 (Soto), 1165 (Abram)
Kind: D
Fidelity: variant: the identification is this package's -/
def ReflectionSoto (T : LO.FirstOrder.ArithmeticTheory) [T.Δ₁] [𝗥₀ ⪯ T]
    (σ : ℕ → ℕ → Sentence) (S : StateSystem) (P : History) {F : ℕ → Prop}
    (hF : ComputablePred F) (Q : ℕ → Finset ℕ) : Prop :=
  E2xσ σ S P ∧ ∀ n, HMExact T (P n) hF (Q n)

/-- `ReflectionSoto` unfolds to its two conjuncts (`rfl`; the mandate's T4.7 asks for nothing more).
Source: bli-soto-a-088
Kind: L
Fidelity: n/a -/
theorem reflectionSoto_iff (T : LO.FirstOrder.ArithmeticTheory) [T.Δ₁] [𝗥₀ ⪯ T]
    (σ : ℕ → ℕ → Sentence) (S : StateSystem) (P : History) {F : ℕ → Prop}
    (hF : ComputablePred F) (Q : ℕ → Finset ℕ) :
    ReflectionSoto T σ S P hF Q ↔ E2xσ σ S P ∧ ∀ n, HMExact T (P n) hF (Q n) := Iff.rfl

end Cleanroom.Bli.BliRvcUi
