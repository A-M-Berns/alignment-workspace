import Cleanroom.Bli.BliExactness.Defs
import Cleanroom.Bli.BliFound.StateSentence
import LogicalInduction.Construction.Freeze.Oracle

/-!
# `bli-exactness` — X3: a computable logical inductor violating exact D-NNU and D-ST-x on day 1

**Construction-facing module** (imports FAF's `thm:ifp` kit through `Construction.Freeze.Oracle`
and the paper market through `bli-found`'s `StateSentence`). The witness `x3History` is FAF's LIA
over `paperDP 𝗜𝚺₁` with **five day-1 prices moved**:

| sentence | day-1 price |
|---|---|
| `φ₀ := atom 1` (small on day 1) | `1` |
| `χ₀ := quoteAt 𝗜𝚺₁ 2 φ₀ 0 ½` ("`0 < 𝑸₂(φ₀) ≤ ½`") | `1` |
| `χ₁ := quoteAt 𝗜𝚺₁ 2 φ₀ ½ 1` ("`½ < 𝑸₂(φ₀) ≤ 1`") | `0` |
| `φ₀ ⋏ χ₀` | `1` |
| `φ₀ ⋏ χ₁` | `0` |

Every other `(day, sentence)` price is the LIA's. **Table changed in repair round 2** (audit r2
adversarial B1): repair round 1's table `φ₀ ↦ ½`, `φ₀ ⋏ χ₀ ↦ ½`, `χ₀ ↦ 1`, `χ₁ ↦ 0` was coherent but
**interval-exact** at the headline cell — the conditional of `φ₀` given `χ₀` was `½ ∈ (0, ½]`, and
`P₁(φ₀) = ½ ∈ [0, ½]` — so its violations (`½ ≠ ¼`, `¼ ≠ ½`) were of the midpoint representative
only, the F5 artifact by this package's own X1 standard. The present table is the point mass of the
single world in which `φ₀` is true and `𝑸₂(φ₀) ∈ (0, ½]`: a market **certain of `φ₀` and certain
that tomorrow it will price `φ₀` at or below `½`** — the intended phenomenon (bli-paper-2-013:
"whenever the day-`n` market expects its price of `φ` to move"). It is consistent with a
probability on all five sentences by construction (`x3_day1_coherent`: the conjunction prices are
the minima, the two cells partition), with the fifth entry `φ₀ ⋏ χ₁ ↦ 0` now in the table rather
than left to an unverified claim about the LIA's day-1 value (audit r2 N2, both lenses). Then on
day 1, with cells `{(0, ½), (½, 1)}`:

* **(α)** interval form (the headline): `P₁(φ₀) = 1 ∉ [∑ lo_I·P₁(χ_I), ∑ hi_I·P₁(χ_I)] = [0, ½]`
  (`x3_not_exactNNUAtInterval`); midpoint corollary `∑_I mid(I)·P₁(χ_I) = ¼·1 + ¾·0 = ¼ ≠ 1`
  (`x3_not_exactNNUAt`, unguarded `ExactNNUAt`; `bli-found`'s guarded `D_NNU` is vacuous on
  day 1, `d_nnu_day1_vacuous` — Known issue 4);
* **(β)** interval form (the headline): the conditional of `φ₀` given `χ₀` is `1 ∉ (0, ½]`,
  i.e. `¬ (0·P₁(χ₀) < P₁(φ₀ ⋏ χ₀) ≤ ½·P₁(χ₀))` (`x3_interval_violation`; family-relative
  corollary `x3_not_exactReflectionInterval`); midpoint corollary `P₁(φ₀ ⋏ χ₀) = 1 ≠ ¼ = mid(0, ½)·P₁(χ₀)`
  (`x3_cell_inequality`, `x3_not_exactSelfTrustX`);
* **What inhabits the refuted predicates**: `sotoBundle_x3Cells_witness` — Soto's two-clause
  bundle market over the same two cells with masses `½` satisfies exact self-trust at FAF's
  `quoteAt 𝗜𝚺₁` on every `n < m`, exact no-net-update at `φ₀`, and prices `φ₀` at `½` (the quote
  family's two injectivity facts, `quoteAt_cellInjective`/`quoteAt_conjDisjoint`, are proved here).
  Graded **N−** (repair round 2): a by-definition valuation, `⊤`-incoherent as every positive-mass
  inhabitant of the midpoint predicate must be (`Defs.lean` `coherentTop_forces_zero`). So the
  midpoint predicate X3's corollaries refute has no non-degenerate inhabitant; the interval
  predicates the headlines refute admit `⊤`-coherent inhabitants in principle, none exhibited
  (report § Open);
* **(γ)** `x3History` **is a computable logical inductor** over `paperDP 𝗜𝚺₁`
  (`x3_isLogicalInductor`): `ComputableMarket` by FAF's `ComputableMarket.ofComputableTable`
  over a five-entry association list patched onto the paper market's own program, finite support
  `{1} × {φ₀, φ₀ ⋏ χ₀, φ₀ ⋏ χ₁, χ₀, χ₁}`, and FAF's corrected `thm:ifp`
  (`FreezeOracle.lic_iff_of_finiteSupport`) from `paperLIA 𝗜𝚺₁`.

Day 2 is untouched (`x3History_eq_lia_of_ne_one`), so `quoteAt 𝗜𝚺₁ 2 φ₀ I` quotes `x3History`'s
**own** day-2 price: the self-trust reading is honest. The recipe (`lookupOr`, `computable_lookupOr`,
`ofComputableTable`, `lic_iff_of_finiteSupport`) is `bli-exact-base`'s `Splice.lean`, copied and
cited, not imported (Known issue 10).

**Why the perturbation is essential** (Known issue 5, finding): the unperturbed LIA prices every
sentence off its finite day-`n` support at `0` (`RationalBeliefState.quote_eq_zero_of_not_mem`),
so on it the exact product identities hold *trivially* at those coordinates; "take the LIA itself"
is not a route to a violation. Contrast: `bli-exact-base`'s `splice_isLogicalInductor` gives an
inductor *satisfying* exact cell-NNU on a segment — the exact/asymptotic gap is two-sided.
-/

namespace Cleanroom.Bli.BliExactness

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound

/-! ## Association-list lookup with fallthrough (precedent: `bli-exact-base` `Splice.lean`) -/

/-- Lookup in a finite association list keyed by `(day, code)`, falling through to `f` when the key
is absent (first match wins).
Source: precedent `bli-exact-base` `Splice.lookupOr` (copied, Known issue 10)
Kind: D
Fidelity: exact -/
def lookupOr : List (ℕ × ℕ × ℚ) → (ℕ → ℕ → ℚ) → ℕ → ℕ → ℚ
  | [], f, n, c => f n c
  | e :: l, f, n, c => if n = e.1 ∧ c = e.2.1 then e.2.2 else lookupOr l f n c

/-- A key matching no entry falls through.
Source: precedent `bli-exact-base` `Splice.lookupOr_eq_of_forall_ne`
Kind: L
Fidelity: n/a -/
lemma lookupOr_eq_of_forall_ne {l : List (ℕ × ℕ × ℚ)} {f : ℕ → ℕ → ℚ} {n c : ℕ}
    (h : ∀ e ∈ l, ¬ (n = e.1 ∧ c = e.2.1)) : lookupOr l f n c = f n c := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    rw [lookupOr, if_neg (h e (by simp))]
    exact ih fun e' he' => h e' (by simp [he'])

/-- A lookup over `[0,1]`-valued entries with a `[0,1]`-valued fallthrough lies in `[0,1]`.
Source: precedent `bli-exact-base` `Splice.lookupOr_mem_Icc`
Kind: L
Fidelity: n/a -/
lemma lookupOr_mem_Icc {l : List (ℕ × ℕ × ℚ)} {f : ℕ → ℕ → ℚ} {n c : ℕ}
    (hl : ∀ e ∈ l, 0 ≤ e.2.2 ∧ e.2.2 ≤ 1) (hf : 0 ≤ f n c ∧ f n c ≤ 1) :
    0 ≤ lookupOr l f n c ∧ lookupOr l f n c ≤ 1 := by
  induction l with
  | nil => exact hf
  | cons e l ih =>
    rw [lookupOr]
    split_ifs
    · exact hl e (by simp)
    · exact ih fun e' he' => hl e' (by simp [he'])

/-- The two unpaired components of `z` are `(a, b)` iff `z = Nat.pair a b`.
Source: precedent `bli-exact-base` `Splice.unpair_eq_iff_eq_pair`
Kind: L
Fidelity: n/a -/
lemma unpair_eq_iff_eq_pair {z a b : ℕ} :
    (z.unpair.1 = a ∧ z.unpair.2 = b) ↔ z = Nat.pair a b := by
  constructor
  · rintro ⟨h1, h2⟩
    calc z = Nat.pair z.unpair.1 z.unpair.2 := (Nat.pair_unpair z).symm
      _ = Nat.pair a b := by rw [h1, h2]
  · rintro rfl
    simp [Nat.unpair_pair]

/-- **A fixed finite association list keeps a computable table computable**: the lookup is a finite
nest of equality tests against constants of the program.
Source: precedent `bli-exact-base` `Splice.computable_lookupOr`; FAF
`LIAPerturbation.computable_perturbedQuote` (the one-entry template)
Kind: C
Fidelity: exact
Hyps: (a) -/
lemma computable_lookupOr (l : List (ℕ × ℕ × ℚ)) {f : ℕ → ℕ → ℚ}
    (hf : Computable fun z : ℕ => Encodable.encode (f z.unpair.1 z.unpair.2)) :
    Computable fun z : ℕ => Encodable.encode (lookupOr l f z.unpair.1 z.unpair.2) := by
  induction l with
  | nil => exact hf
  | cons e l ih =>
    have htest : Computable fun z : ℕ => decide (z = Nat.pair e.1 e.2.1) :=
      (Primrec.eq.comp Primrec.id (Primrec.const (Nat.pair e.1 e.2.1))).decide.to_comp
    refine (Computable.cond htest (Computable.const (Encodable.encode e.2.2)) ih).of_eq
      fun z => ?_
    by_cases hz : z = Nat.pair e.1 e.2.1
    · have hu : z.unpair.1 = e.1 ∧ z.unpair.2 = e.2.1 := unpair_eq_iff_eq_pair.2 hz
      simp [lookupOr, hz]
    · have hu : ¬ (z.unpair.1 = e.1 ∧ z.unpair.2 = e.2.1) :=
        fun h => hz (unpair_eq_iff_eq_pair.1 h)
      simp [lookupOr, hz, hu]

/-! ## Sentence shape discriminators -/

/-- Whether a sentence is a conjunction (for constructor-disjointness arguments).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def isAnd : Sentence → Bool
  | .and _ _ => true
  | _ => false

/-- `isAnd` on a conjunction, an atom and a negation.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma isAnd_wedge (φ ψ : Sentence) : isAnd (φ ⋏ ψ) = true := rfl

/-- `isAnd` on an atom.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma isAnd_atom (a : ℕ) : isAnd (Formula.atom a) = false := rfl

/-- `isAnd` on a negation (`∼φ = φ 🡒 ⊥`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma isAnd_neg (φ : Sentence) : isAnd (∼φ) = false := rfl

section Thresholds

variable (T : LO.FirstOrder.ArithmeticTheory) [T.Δ₁] [𝗥₀ ⪯ T]

/-- The threshold literal of the market's quote LUV is a quotation atom at the packed
`⟨code, ⟨⟨m, ⌜φ⌝⟩, ⌜r⌝⟩⟩`.
Source: FAF `arithmeticThresholdLUV`, `RationalQuoteCode.luv`; `bli-found` `quoteLuv`
Kind: L
Fidelity: n/a -/
lemma quoteLuv_gt_eq (m : ℕ) (φ : Sentence) (r : ℚ) :
    (quoteLuv T m φ).gt r = Formula.atom (quotationClaimCode universalQuotePos universalQuoteNeg
      (Nat.pair (marketQuoteCode T).code
        (Nat.pair (Nat.pair m (Encodable.encode φ)) (Encodable.encode r)))) := rfl

/-- The threshold literals are injective in the threshold.
Source: none: infrastructure (`Nat.pair` and `Encodable.encode` are injective)
Kind: L
Fidelity: n/a -/
lemma quoteLuv_gt_injective (m : ℕ) (φ : Sentence) :
    Function.Injective fun r : ℚ => (quoteLuv T m φ).gt r := by
  intro r s h
  have h' : Encodable.encode r = Encodable.encode s := by
    simpa [quoteLuv_gt_eq, quotationClaimCode, Nat.pair_eq_pair] using h
  exact Encodable.encode_injective h'

/-- Two threshold literals of the market's quote LUV that coincide have the same threshold,
whatever their days and quoted sentences (the payload `⟨code, ⟨⟨m, ⌜φ⌝⟩, ⌜r⌝⟩⟩` is injective in
each component).
Source: none: infrastructure (`Nat.pair` and `Encodable.encode` are injective)
Kind: L
Fidelity: n/a -/
lemma quoteLuv_gt_threshold_eq {m m' : ℕ} {φ φ' : Sentence} {r s : ℚ}
    (h : (quoteLuv T m φ).gt r = (quoteLuv T m' φ').gt s) : r = s := by
  rw [quoteLuv_gt_eq, quoteLuv_gt_eq] at h
  have h1 := Formula.atom.inj h
  unfold quotationClaimCode at h1
  have h2 := (Nat.pair_eq_pair.1 h1).2
  have h3 := (Nat.pair_eq_pair.1 h2).2
  have h4 := (Nat.pair_eq_pair.1 h3).2
  have h5 := (Nat.pair_eq_pair.1 h4).2
  have h6 := (Nat.pair_eq_pair.1 h5).2
  exact Encodable.encode_injective h6

/-- **`bli-found`'s `quoteAt T` is cell-injective** (for every cell family): two coinciding
interval quotes name the same cell. Discharges `Defs.lean`'s `CellInjective` hypothesis.
Source: none: infrastructure (hypothesis of `sotoBundle_quote`)
Kind: L
Fidelity: n/a -/
theorem quoteAt_cellInjective (cells : ℕ → Finset (ℚ × ℚ)) : CellInjective (quoteAt T) cells := by
  intro m m' φ φ' I I' _ _ h
  rw [quoteAt, quoteAt, Formula.and_inj, Formula.neg_inj] at h
  exact Prod.ext (quoteLuv_gt_threshold_eq T h.1) (quoteLuv_gt_threshold_eq T h.2)

/-- **A conjunction `φ ⋏ quoteAt …` is never itself an interval quote** (an interval quote's right
conjunct is a negation, a conjunction's right conjunct here is a conjunction). Discharges
`Defs.lean`'s `ConjDisjoint` hypothesis.
Source: none: infrastructure (hypothesis of `sotoBundle_conj`)
Kind: L
Fidelity: n/a -/
theorem quoteAt_conjDisjoint : ConjDisjoint (quoteAt T) := by
  intro m m' φ φ' lo hi lo' hi' h
  have h' : φ ⋏ quoteAt T m φ lo hi =
      (quoteLuv T m' φ').gt lo' ⋏ ∼ (quoteLuv T m' φ').gt hi' := h
  have := congrArg isAnd (Formula.and_inj.1 h').2
  rw [isAnd_neg, quoteAt, isAnd_wedge] at this
  exact absurd this (by decide)

/-- **Every non-conjunction is object-level for FAF's quote family**: a cell sentence
`quoteAt T m φ lo hi` and a conjunction `φ ⋏ quoteAt …` are both conjunctions, so a sentence with
`isAnd ψ = false` is neither.
Source: none: infrastructure (discharges `ObjectLevel` at `quoteAt T`)
Kind: L
Fidelity: n/a -/
theorem objectLevel_quoteAt_of_not_isAnd {ψ : Sentence} (hψ : isAnd ψ = false) :
    ObjectLevel (quoteAt T) ψ := by
  refine ⟨fun m φ lo hi h => ?_, fun m φ lo hi h => ?_⟩
  · have := congrArg isAnd h
    rw [hψ, quoteAt, isAnd_wedge] at this
    exact Bool.false_ne_true this
  · have := congrArg isAnd h
    rw [hψ, isAnd_wedge] at this
    exact Bool.false_ne_true this

/-- `isAnd` on `⊤` (`= ⊥ 🡒 ⊥`, not a conjunction).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma isAnd_top : isAnd (⊤ : Sentence) = false := rfl

/-- Atoms and `⊤` are object-level for `quoteAt T`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem objectLevel_quoteAt_atom (a : ℕ) : ObjectLevel (quoteAt T) (Formula.atom a) :=
  objectLevel_quoteAt_of_not_isAnd T (isAnd_atom a)

/-- `⊤` is object-level for `quoteAt T`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem objectLevel_quoteAt_top : ObjectLevel (quoteAt T) (⊤ : Sentence) :=
  objectLevel_quoteAt_of_not_isAnd T isAnd_top

/-- **Soto's two-clause bundle market at FAF's own quote family satisfies exact self-trust on any
cell family** (`Defs.lean` `sotoBundle_exactSelfTrustX` with both injectivity facts discharged), for
every mass function `w`. Grade **N−** for `ExactSelfTrustX (quoteAt T) cells` (repair round 2): a
by-definition valuation, `⊤`-incoherent wherever it has positive mass on a cell of midpoint `≠ 1`
(`sotoBundle_top_incoherent`), as every such inhabitant must be (`coherentTop_forces_zero`).
`sotoBundle_x3Cells_witness` below records what it does establish at X3's two-cell family.
Source: Soto PDF 20 p. 1–2 ([[bli-soto-b-inventory]] 025); mandate X6 (v) (non-vacuity);
audit r2 fidelity B1 (i), adversarial B2 (ii)
Kind: N-
Fidelity: n/a
Hyps: (a) -/
theorem quoteAt_sotoBundle_exactSelfTrustX (cells : ℕ → Finset (ℚ × ℚ)) (w : ℚ × ℚ → ℝ) :
    ExactSelfTrustX (quoteAt T) cells (sotoBundleHistory (quoteAt T) cells w) :=
  sotoBundle_exactSelfTrustX (quoteAt_cellInjective T cells) (quoteAt_conjDisjoint T) w

/-- **Soto's two-clause bundle market at `quoteAt T` satisfies exact no-net-update at every
non-conjunction, every day** — the Reflection clause (`Defs.lean` `sotoBundle_exactNNUAt`).
Source: Soto PDF 20 p. 1 (the Reflection clause); audit r2 fidelity B1 (i)
Kind: L
Fidelity: exact (Soto's `n = 1` clause at FAF's quote family)
Hyps: (a) -/
theorem quoteAt_sotoBundle_exactNNUAt_of_not_isAnd (cells : ℕ → Finset (ℚ × ℚ)) (w : ℚ × ℚ → ℝ)
    (n : ℕ) {ψ : Sentence} (hψ : isAnd ψ = false) :
    ExactNNUAt (quoteAt T) cells (sotoBundleHistory (quoteAt T) cells w) n ψ :=
  sotoBundle_exactNNUAt (quoteAt_cellInjective T cells) w n (objectLevel_quoteAt_of_not_isAnd T hψ)

/-- **Soto's `n = 1` bundle market at `quoteAt T` prices `⊤` strictly below `1`** for any
probability `w` on a family of cells of midpoint `< 1` — the Lean form of findings F15 (PDF 20 p. 2's
"coherence … translated into our derived object-level beliefs" holds only up to the cell
half-width). `Defs.lean` `sotoBundle_top_lt_one` with `⊤` object-level discharged.
Source: Soto PDF 20 p. 1–2 ([[bli-soto-b-inventory]] 025, 027); audit r2 adversarial B2 (iv)
Kind: P
Fidelity: exact (Soto's `n = 1` market at FAF's quote family; any family of cells inside `[0, 1]`)
Hyps: (a) -/
theorem quoteAt_sotoBundle_top_lt_one (cells : ℕ → Finset (ℚ × ℚ)) (w : ℚ × ℚ → ℝ) (n : ℕ)
    (hw : ∀ I ∈ cells (n + 1), 0 ≤ w I) (hsum : ∑ I ∈ cells (n + 1), w I = 1)
    (hmid : ∀ I ∈ cells (n + 1), mid I < 1) :
    sotoBundleHistory (quoteAt T) cells w n (⊤ : Sentence) < 1 :=
  sotoBundle_top_lt_one w n (objectLevel_quoteAt_top T) hw hsum hmid

/-- **No interval quote is small on day 1**: `quoteAt T m φ lo hi` is a conjunction of an atom and
a negated atom, of token size `≥ 11 > 4 = sizeBound 1`. So `bli-found`'s `D_NNU` guard
`SmallOn n (quoteAt (n+1) φ I)` fails on day `n = 1` for every cell (Known issue 4).
Source: mandate Known issue 4; `bli-found` `sizeBound`, `tokenSize_and`, `tokenSize_neg`
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem not_smallOn_one_quoteAt (m : ℕ) (φ : Sentence) (lo hi : ℚ) :
    ¬ SmallOn 1 (quoteAt T m φ lo hi) := by
  unfold SmallOn
  rw [quoteAt, quoteLuv_gt_eq, quoteLuv_gt_eq, tokenSize_and, tokenSize_neg]
  have h1 := three_le_tokenSize_atom (quotationClaimCode universalQuotePos universalQuoteNeg
    (Nat.pair (marketQuoteCode T).code
      (Nat.pair (Nat.pair m (Encodable.encode φ)) (Encodable.encode lo))))
  have h2 := three_le_tokenSize_atom (quotationClaimCode universalQuotePos universalQuoteNeg
    (Nat.pair (marketQuoteCode T).code
      (Nat.pair (Nat.pair m (Encodable.encode φ)) (Encodable.encode hi))))
  have hs : sizeBound 1 = 4 := by norm_num [sizeBound]
  omega

/-- **`D_NNU`'s day-1 clause is vacuous** (finding, severity imprecision): for every nonempty cell
family, every history `Q`, every `ε` and every day-1 small `φ`, the day-1 instance of
`bli-found`'s `D_NNU quoteAt cells ε Q` holds — its guard is false. The violated object of X3 is
therefore the unguarded `ExactNNUAt`.
Source: mandate Known issue 4; `bli-found` `D_NNU`
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem d_nnu_day1_vacuous (cells : ℕ → Finset (ℚ × ℚ)) (hne : (cells 2).Nonempty)
    (Q : History) (ε : ℕ → ℝ) (φ : Sentence) (_hφ : φ ∈ smallSet 1)
    (hguard : ∀ I ∈ cells (1 + 1), SmallOn 1 (quoteAt T (1 + 1) φ I.1 I.2)) :
    |∑ I ∈ cells (1 + 1), (((I.1 + I.2) / 2 : ℚ) : ℝ) * Q 1 (quoteAt T (1 + 1) φ I.1 I.2) - Q 1 φ|
      ≤ ε (1 + 1) := by
  exfalso
  obtain ⟨I, hI⟩ := hne
  exact not_smallOn_one_quoteAt T _ _ _ _ (hguard I hI)

end Thresholds


/-! ## The X3 data -/

/-- `φ₀ := atom 1`, small on day 1 (`bli-found` `smallOn_atom_self`).
Source: mandate X3
Kind: D
Fidelity: exact -/
def x3Atom : Sentence := Formula.atom 1

/-- The two day-2 cells `(0, ½]`, `(½, 1]`.
Source: mandate X3
Kind: D
Fidelity: exact -/
def x3Cells : ℕ → Finset (ℚ × ℚ) := fun _ => {(0, 1 / 2), (1 / 2, 1)}

/-- `χ₀ := ⌜0 < 𝑸₂(φ₀) ≤ ½⌝`.
Source: mandate X3
Kind: D
Fidelity: exact -/
noncomputable def x3CellLo : Sentence := quoteAt 𝗜𝚺₁ 2 x3Atom 0 (1 / 2)

/-- `χ₁ := ⌜½ < 𝑸₂(φ₀) ≤ 1⌝`.
Source: mandate X3
Kind: D
Fidelity: exact -/
noncomputable def x3CellHi : Sentence := quoteAt 𝗜𝚺₁ 2 x3Atom (1 / 2) 1

/-- `φ₀ ⋏ χ₀`.
Source: mandate X3
Kind: D
Fidelity: exact -/
noncomputable def x3Conj : Sentence := x3Atom ⋏ x3CellLo

/-- `φ₀ ⋏ χ₁` — the fifth moved sentence (repair round 2): put in the table at `0` so that the
day-1 table is a point mass on all five sentences by construction, rather than relying on an
unverified claim about the LIA's day-1 price of it (audit r2 N2, both lenses).
Source: audit r2 fidelity N2 / adversarial N2
Kind: D
Fidelity: exact -/
noncomputable def x3ConjHi : Sentence := x3Atom ⋏ x3CellHi

/-- The five moved sentences are pairwise distinct (constructor disjointness and threshold
injectivity).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma x3_distinct :
    x3Atom ≠ x3CellLo ∧ x3Atom ≠ x3CellHi ∧ x3Atom ≠ x3Conj ∧
      x3Conj ≠ x3CellLo ∧ x3Conj ≠ x3CellHi ∧ x3CellLo ≠ x3CellHi ∧
      x3Atom ≠ x3ConjHi ∧ x3ConjHi ≠ x3CellLo ∧ x3ConjHi ≠ x3CellHi ∧ x3Conj ≠ x3ConjHi := by
  have hLoHi : x3CellLo ≠ x3CellHi := by
    intro h
    rw [x3CellLo, x3CellHi, quoteAt, quoteAt, Formula.and_inj] at h
    have := quoteLuv_gt_injective 𝗜𝚺₁ 2 x3Atom h.1
    norm_num at this
  refine ⟨?_, ?_, ?_, ?_, ?_, hLoHi, ?_, ?_, ?_, ?_⟩
  · intro h; have := congrArg isAnd h
    rw [x3Atom, isAnd_atom, x3CellLo, quoteAt, isAnd_wedge] at this; exact Bool.false_ne_true this
  · intro h; have := congrArg isAnd h
    rw [x3Atom, isAnd_atom, x3CellHi, quoteAt, isAnd_wedge] at this; exact Bool.false_ne_true this
  · intro h; have := congrArg isAnd h
    rw [x3Atom, isAnd_atom, x3Conj, isAnd_wedge] at this; exact Bool.false_ne_true this
  · intro h
    have h' : x3Atom ⋏ x3CellLo =
        (quoteLuv 𝗜𝚺₁ 2 x3Atom).gt 0 ⋏ ∼ (quoteLuv 𝗜𝚺₁ 2 x3Atom).gt (1 / 2) := h
    have := congrArg isAnd (Formula.and_inj.1 h').2
    rw [isAnd_neg, x3CellLo, quoteAt, isAnd_wedge] at this; exact absurd this (by decide)
  · intro h
    have h' : x3Atom ⋏ x3CellLo =
        (quoteLuv 𝗜𝚺₁ 2 x3Atom).gt (1 / 2) ⋏ ∼ (quoteLuv 𝗜𝚺₁ 2 x3Atom).gt 1 := h
    have := congrArg isAnd (Formula.and_inj.1 h').2
    rw [isAnd_neg, x3CellLo, quoteAt, isAnd_wedge] at this; exact absurd this (by decide)
  · intro h; have := congrArg isAnd h
    rw [x3Atom, isAnd_atom, x3ConjHi, isAnd_wedge] at this; exact Bool.false_ne_true this
  · intro h
    have h' : x3Atom ⋏ x3CellHi =
        (quoteLuv 𝗜𝚺₁ 2 x3Atom).gt 0 ⋏ ∼ (quoteLuv 𝗜𝚺₁ 2 x3Atom).gt (1 / 2) := h
    have := congrArg isAnd (Formula.and_inj.1 h').2
    rw [isAnd_neg, x3CellHi, quoteAt, isAnd_wedge] at this; exact absurd this (by decide)
  · intro h
    have h' : x3Atom ⋏ x3CellHi =
        (quoteLuv 𝗜𝚺₁ 2 x3Atom).gt (1 / 2) ⋏ ∼ (quoteLuv 𝗜𝚺₁ 2 x3Atom).gt 1 := h
    have := congrArg isAnd (Formula.and_inj.1 h').2
    rw [isAnd_neg, x3CellHi, quoteAt, isAnd_wedge] at this; exact absurd this (by decide)
  · intro h
    rw [x3Conj, x3ConjHi, Formula.and_inj] at h
    exact hLoHi h.2

/-- The five day-1 entries, keyed by `(1, code)`: the point mass of the world in which `φ₀` is true
and `𝑸₂(φ₀) ∈ (0, ½]`.
Source: mandate X3 (`tbl`), values changed in repair rounds 1 and 2 (see the module header)
Kind: D
Fidelity: variant: the mandate's table had `φ₀ ↦ 1`, `φ₀ ⋏ χ₀ ↦ 0` (incoherent); repair round 1's
had `φ₀ ↦ ½`, `φ₀ ⋏ χ₀ ↦ ½` (interval-exact); this one is a point mass violating both forms -/
noncomputable def x3Entries : List (ℕ × ℕ × ℚ) :=
  [(1, Encodable.encode x3Atom, 1), (1, Encodable.encode x3Conj, 1),
   (1, Encodable.encode x3CellLo, 1), (1, Encodable.encode x3CellHi, 0),
   (1, Encodable.encode x3ConjHi, 0)]

/-- **The exact rational table of the witness**: the five entries, else the paper market's own
quote `paperQuote 𝗜𝚺₁ n c`.
Source: mandate X3 (`P'`)
Kind: D
Fidelity: exact -/
noncomputable def x3Quote (n c : ℕ) : ℚ := lookupOr x3Entries (paperQuote 𝗜𝚺₁) n c

/-- **The witness market** `x3History`: the real cast of `x3Quote` at the sentence's code.
Source: mandate X3 (`P'`), judged item 2
Kind: D
Fidelity: exact -/
noncomputable def x3History : History :=
  fun n ψ => (x3Quote n (Encodable.encode ψ) : ℝ)

/-- The support of the perturbation: five `(day, sentence)` pairs on day 1.
Source: mandate X3 (`S ×ˢ {1}`)
Kind: D
Fidelity: exact -/
noncomputable def x3Support : Finset (ℕ × Sentence) :=
  {(1, x3Atom), (1, x3Conj), (1, x3CellLo), (1, x3CellHi), (1, x3ConjHi)}

/-- Day-1 values of the witness at the five moved sentences.
Source: mandate X3 (`tbl`)
Kind: L
Fidelity: exact -/
lemma x3History_day1 :
    x3History 1 x3Atom = 1 ∧ x3History 1 x3Conj = 1 ∧
      x3History 1 x3CellLo = 1 ∧ x3History 1 x3CellHi = 0 ∧ x3History 1 x3ConjHi = 0 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := x3_distinct
  have e1 := Encodable.encode_injective.ne h1
  have e2 := Encodable.encode_injective.ne h2
  have e3 := Encodable.encode_injective.ne h3
  have e4 := Encodable.encode_injective.ne h4
  have e5 := Encodable.encode_injective.ne h5
  have e6 := Encodable.encode_injective.ne h6
  have e7 := Encodable.encode_injective.ne h7
  have e8 := Encodable.encode_injective.ne h8
  have e9 := Encodable.encode_injective.ne h9
  have e10 := Encodable.encode_injective.ne h10
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [x3History, x3Quote, x3Entries, lookupOr, e8, e9, Ne.symm e1, Ne.symm e2, Ne.symm e3,
      Ne.symm e4, Ne.symm e5, Ne.symm e6, Ne.symm e7, Ne.symm e10]

/-- **The day-1 table is a point mass on the five sentences** (repair round 2, replacing the
hand-checked four-sentence coherence claim): the two conjunction prices are the minima of their
conjuncts' prices, and the two cells' prices sum to `1` — exactly the `{0, 1}`-valuation of the
world in which `φ₀` holds and `𝑸₂(φ₀) ∈ (0, ½]`. So the violations below are not a by-product of
propositional incoherence on the moved sentences (audit r1 adversarial N2, r2 N2).
Source: audit r1 adversarial N2; audit r2 adversarial B1 (i) ("consistent with a probability on the
five sentences")
Kind: L
Fidelity: n/a -/
theorem x3_day1_coherent :
    x3History 1 x3Conj = min (x3History 1 x3Atom) (x3History 1 x3CellLo) ∧
      x3History 1 x3ConjHi = min (x3History 1 x3Atom) (x3History 1 x3CellHi) ∧
      x3History 1 x3CellLo + x3History 1 x3CellHi = 1 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := x3History_day1
  rw [h1, h2, h3, h4, h5]
  norm_num

/-- Off the five moved pairs the witness is the LIA.
Source: mandate X3; FAF `FiniteSupportPerturbation`
Kind: L
Fidelity: exact -/
theorem x3History_eq_lia_of_not_mem {d : ℕ} {ψ : Sentence} (h : (d, ψ) ∉ x3Support) :
    x3History d ψ = liaHistory (paperDP 𝗜𝚺₁) d ψ := by
  unfold x3History x3Quote
  rw [lookupOr_eq_of_forall_ne, ← paperQuote_eq_liaHistory]
  intro e he ⟨hd, hc⟩
  simp only [x3Entries, List.mem_cons, List.mem_nil_iff, or_false] at he
  apply h
  rcases he with rfl | rfl | rfl | rfl | rfl <;>
    simp only at hd hc <;> subst hd <;> rw [Encodable.encode_injective hc] <;>
    simp [x3Support]

/-- **Day 2 (and every day `≠ 1`) is untouched**: `quoteAt 𝗜𝚺₁ 2 φ₀ I` quotes `x3History`'s own
day-2 price — the self-trust reading of (β) is honest.
Source: mandate X3 ("only day-1 prices move")
Kind: L
Fidelity: exact -/
theorem x3History_eq_lia_of_ne_one {d : ℕ} (hd : d ≠ 1) (ψ : Sentence) :
    x3History d ψ = liaHistory (paperDP 𝗜𝚺₁) d ψ := by
  apply x3History_eq_lia_of_not_mem
  simp [x3Support, hd]

/-- The witness is a finite-support perturbation of the LIA.
Source: mandate X3; FAF `FiniteSupportPerturbation` (`Properties/FinitePerturbations.lean:439`)
Kind: L
Fidelity: exact -/
theorem x3_finiteSupportPerturbation :
    FiniteSupportPerturbation (liaHistory (paperDP 𝗜𝚺₁)) x3History :=
  ⟨x3Support, fun _ _ h => (x3History_eq_lia_of_not_mem h).symm⟩

/-- The witness table is computable in the paper's sense: the paper market's program along the
paired input, patched by the five-entry list.
Source: mandate X3; FAF `MarketComputation.quote_comp_computable`
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem x3Quote_computable :
    Computable fun z : ℕ => Encodable.encode (x3Quote z.unpair.1 z.unpair.2) := by
  unfold x3Quote
  refine computable_lookupOr _ ?_
  have := (paperMarketComputation 𝗜𝚺₁).quote_comp_computable
    (Computable.fst.comp Computable.unpair) (Computable.snd.comp Computable.unpair)
  exact Computable.encode.comp this

/-- **The witness is a computable market** (`def:market`): range in `[0,1]`, exact rational table
`x3Quote`, and a program for it.
Source: mandate X3 (γ); FAF `ComputableMarket.ofComputableTable` (`Framework/Criterion.lean:1091`)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem x3_computableMarket : ComputableMarket x3History := by
  refine ComputableMarket.ofComputableTable x3Quote ?_ (fun _ _ => rfl) x3Quote_computable
  intro n φ
  have hl : ∀ e ∈ x3Entries, 0 ≤ e.2.2 ∧ e.2.2 ≤ 1 := by
    simp only [x3Entries, List.mem_cons, List.mem_nil_iff, or_false]
    rintro e (rfl | rfl | rfl | rfl | rfl) <;> norm_num
  have h := lookupOr_mem_Icc (f := paperQuote 𝗜𝚺₁) hl (paperQuote_mem 𝗜𝚺₁ n φ)
    (c := Encodable.encode φ)
  show (0 : ℝ) ≤ ((lookupOr x3Entries (paperQuote 𝗜𝚺₁) n (Encodable.encode φ) : ℚ) : ℝ) ∧
    ((lookupOr x3Entries (paperQuote 𝗜𝚺₁) n (Encodable.encode φ) : ℚ) : ℝ) ≤ 1
  exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩

/-- **(γ) — the witness is a logical inductor over `paperDP 𝗜𝚺₁`**: FAF's corrected `thm:ifp`
(`FreezeOracle.lic_iff_of_finiteSupport`) from `paperLIA 𝗜𝚺₁`, with no hypothesis on the five
moved prices beyond the `[0,1]` range.
Source: mandate X3 (γ), judged item 2; FAF `lic_iff_of_finiteSupportPerturbation` (`API.lean:597`),
`paperLIA` (`Construction/Paper/TheoremDP.lean:442`); precedent `bli-exact-base`
`splice_isLogicalInductor`
Kind: C
Fidelity: exact
Hyps: (a) `paperLIA`, `thm:ifp`, `x3_computableMarket`, `x3_finiteSupportPerturbation` -/
theorem x3_isLogicalInductor : IsLogicalInductor x3History (paperDP 𝗜𝚺₁) :=
  (FreezeOracle.lic_iff_of_finiteSupport (liaHistory (paperDP 𝗜𝚺₁)) x3History (paperDP 𝗜𝚺₁)
    (paperLIA 𝗜𝚺₁).marketComputable x3_computableMarket x3_finiteSupportPerturbation).mp
    (paperLIA 𝗜𝚺₁)

/-! ## The violations: interval forms (headlines) and midpoint forms (corollaries) -/

/-- **(α) — exact no-net-update fails on day 1 at `φ₀`, in the interval form** — the headline for
(α): `P₁(φ₀) = 1` lies outside `[∑ lo_I·P₁(χ_I), ∑ hi_I·P₁(χ_I)] = [0·1 + ½·0, ½·1 + 1·0] = [0, ½]`.
A market certain of `φ₀` that is certain tomorrow's price of `φ₀` will be at most `½` — it expects
its own price to move (bli-paper-2-013), which is what no-net-update forbids. Not the F5 artifact:
the midpoint form `x3_not_exactNNUAt` follows (`ExactNNUAt.interval`), not the other way round.
Source: mandate X3 (α); bli-paper-2-008 (c) (the exact form is "too strong"); bli-paper-2-013;
judged item 2; audit r2 adversarial B1 (i)
Kind: N+
Fidelity: exact (unguarded interval form of `D_NNU`'s body; see `d_nnu_day1_vacuous`)
Hyps: (a) -/
theorem x3_not_exactNNUAtInterval :
    ¬ ExactNNUAtInterval (quoteAt 𝗜𝚺₁) x3Cells x3History 1 x3Atom := by
  obtain ⟨h1, -, h3, h4, -⟩ := x3History_day1
  unfold ExactNNUAtInterval
  have hne : ((0 : ℚ), (1 / 2 : ℚ)) ≠ (1 / 2, 1) := by norm_num
  show ¬ ((∑ I ∈ ({(0, 1 / 2), (1 / 2, 1)} : Finset (ℚ × ℚ)),
        ((I.1 : ℚ) : ℝ) * x3History 1 (quoteAt 𝗜𝚺₁ 2 x3Atom I.1 I.2)) ≤ x3History 1 x3Atom ∧
      x3History 1 x3Atom ≤ ∑ I ∈ ({(0, 1 / 2), (1 / 2, 1)} : Finset (ℚ × ℚ)),
        ((I.2 : ℚ) : ℝ) * x3History 1 (quoteAt 𝗜𝚺₁ 2 x3Atom I.1 I.2))
  rw [Finset.sum_pair hne, Finset.sum_pair hne]
  change ¬ (((0 : ℚ) : ℝ) * x3History 1 x3CellLo + ((1 / 2 : ℚ) : ℝ) * x3History 1 x3CellHi ≤
      x3History 1 x3Atom ∧
    x3History 1 x3Atom ≤
      ((1 / 2 : ℚ) : ℝ) * x3History 1 x3CellLo + ((1 : ℚ) : ℝ) * x3History 1 x3CellHi)
  rw [h1, h3, h4]
  norm_num

/-- **(α), midpoint corollary — exact no-net-update fails on day 1 at `φ₀`**: `¼·1 + ¾·0 = ¼ ≠ 1`.
Implied by the interval violation (`ExactNNUAt.interval`); stated directly.
Source: mandate X3 (α); bli-paper-2-008 (c); judged item 2
Kind: N+
Fidelity: exact (unguarded `ExactNNUAt`; see `d_nnu_day1_vacuous`)
Hyps: (a) -/
theorem x3_not_exactNNUAt : ¬ ExactNNUAt (quoteAt 𝗜𝚺₁) x3Cells x3History 1 x3Atom := by
  obtain ⟨h1, -, h3, h4, -⟩ := x3History_day1
  unfold ExactNNUAt
  have hne : ((0 : ℚ), (1 / 2 : ℚ)) ≠ (1 / 2, 1) := by norm_num
  show ¬ (∑ I ∈ ({(0, 1 / 2), (1 / 2, 1)} : Finset (ℚ × ℚ)),
      ((mid I : ℚ) : ℝ) * x3History 1 (quoteAt 𝗜𝚺₁ 2 x3Atom I.1 I.2) = x3History 1 x3Atom)
  rw [Finset.sum_pair hne]
  change ¬ (((mid (0, 1 / 2) : ℚ) : ℝ) * x3History 1 x3CellLo +
    ((mid (1 / 2, 1) : ℚ) : ℝ) * x3History 1 x3CellHi = x3History 1 x3Atom)
  rw [h1, h3, h4]
  norm_num [mid]

/-- **(β) — exact self-trust / reflection fails on day 1 at `(φ₀, cell (0, ½])`, in the interval
form** — the headline for (β): the conditional of `φ₀` given "`0 < 𝑸₂(φ₀) ≤ ½`" is `1 ∉ (0, ½]`,
i.e. `¬ (0·P₁(χ₀) < P₁(φ₀ ⋏ χ₀) ≤ ½·P₁(χ₀))` with `P₁(φ₀ ⋏ χ₀) = 1`, `P₁(χ₀) = 1`. The cell `(0, ½]`
is a legitimate member of the mandated two-cell family, and `χ₀` quotes `x3History`'s **own** day-2
price (`x3History_eq_lia_of_ne_one`), so this is self-trust about oneself. The statement shape is
the negated conclusion of `exact_reflection_fails_liar`, now violated by a logical inductor at an
ordinary atom. Not the F5 artifact: the midpoint form `x3_cell_inequality` follows
(`ExactReflection.interval`), not the other way round.
Source: mandate X3 (β); [[bli-soto-b-inventory]] 027 (ii) ("strictly stronger"); judged item 2;
audit r2 adversarial B1 (i)
Kind: N+
Fidelity: exact (interval form)
Hyps: (a) -/
theorem x3_interval_violation :
    ¬ (((0 : ℚ) : ℝ) * x3History 1 x3CellLo < x3History 1 x3Conj ∧
        x3History 1 x3Conj ≤ ((1 / 2 : ℚ) : ℝ) * x3History 1 x3CellLo) := by
  obtain ⟨-, h2, h3, -, -⟩ := x3History_day1
  rw [h2, h3]
  norm_num

/-- **(β), midpoint corollary — the cell inequality**: `P₁(φ₀ ⋏ χ₀) = 1 ≠ ¼ = mid(0, ½)·P₁(χ₀)`.
Implied by the interval violation (`ExactReflection.interval`); stated directly.
Source: mandate X3 (β); [[bli-soto-b-inventory]] 027 (ii); judged item 2; audit r1 fidelity B2 (ii)
Kind: N+
Fidelity: exact (midpoint form)
Hyps: (a) -/
theorem x3_cell_inequality :
    x3History 1 x3Conj ≠ ((mid (0, 1 / 2) : ℚ) : ℝ) * x3History 1 x3CellLo := by
  obtain ⟨-, h2, h3, -, -⟩ := x3History_day1
  rw [h2, h3]
  norm_num [mid]

/-- Corollary: the witness does not satisfy `ExactReflectionInterval`/`ExactSelfTrustXInterval` on
the mandated family `x3Cells` — the family-relative **interval** predicate, the refuted object of
record.
Source: mandate X3 (β); audit r2 adversarial B2 (iii) (α)
Kind: L
Fidelity: exact (family-relative, interval form)
Hyps: (a) -/
theorem x3_not_exactReflectionInterval :
    ¬ ExactReflectionInterval (quoteAt 𝗜𝚺₁) x3Cells x3History := by
  intro h
  obtain ⟨-, -, h3, -, -⟩ := x3History_day1
  have hpos : 0 < x3History 1 x3CellLo := by rw [h3]; norm_num
  have hI : ((0 : ℚ), (1 / 2 : ℚ)) ∈ x3Cells 2 := by simp [x3Cells]
  have key := h 1 2 (by norm_num) x3Atom ((0 : ℚ), (1 / 2 : ℚ)) hI hpos
  dsimp only at key
  exact x3_interval_violation key

/-- Corollary: the witness does not satisfy `ExactSelfTrustX`/`ExactReflection` on the mandated
family `x3Cells` (the midpoint predicate; implied by `x3_not_exactReflectionInterval` on
non-degenerate cells, stated directly).
Source: mandate X3 (β)
Kind: L
Fidelity: exact (family-relative, midpoint form)
Hyps: (a) -/
theorem x3_not_exactSelfTrustX : ¬ ExactSelfTrustX (quoteAt 𝗜𝚺₁) x3Cells x3History := by
  intro h
  have := h 1 2 (by norm_num) x3Atom (0, 1 / 2) (by simp [x3Cells])
  exact x3_cell_inequality this

/-- Corollaries: the witness is neither `ExactNNUInterval` nor `ExactNNU` (hence not
`ExactReflectionAllCells` either).
Source: mandate X3
Kind: L
Fidelity: exact -/
theorem x3_not_exactNNUInterval : ¬ ExactNNUInterval (quoteAt 𝗜𝚺₁) x3Cells x3History :=
  fun h => x3_not_exactNNUAtInterval (h 1 x3Atom)

/-- The midpoint everywhere-form corollary.
Source: mandate X3
Kind: L
Fidelity: exact -/
theorem x3_not_exactNNU : ¬ ExactNNU (quoteAt 𝗜𝚺₁) x3Cells x3History :=
  fun h => x3_not_exactNNUAt (h 1 x3Atom)

/-- **X3 assembled**: a computable logical inductor over `paperDP 𝗜𝚺₁` that violates exact
no-net-update and exact self-trust on day 1 **in the interval forms** (and so in the midpoint
forms) — the exact/asymptotic distinction the BLI program rests on is non-vacuous at interval
resolution, and bli-soto-b-027 (ii) ("an LI satisfying Thm 4.12.4 need not satisfy exact
self-trust at any finite time") is witnessed at day 1. The day-1 table is a point mass on the five
moved sentences (`x3_day1_coherent`), so the violation is not a by-product of propositional
incoherence; what X3 shows is that the LIC constrains no finite day (`lic_iff_of_finiteSupport`),
*including* days on which the market is coherent on the sentences in question — including an LI
certain of `φ₀` and certain it will price `φ₀` at or below `½` tomorrow.
Source: mandate X3, judged item 2; bli-paper-2-008 (c); [[bli-soto-b-inventory]] 027 (ii);
audit r2 adversarial B1 (i)
Kind: N+
Fidelity: exact (interval forms; midpoint forms as corollaries)
Hyps: (a) -/
theorem x3_witness :
    IsLogicalInductor x3History (paperDP 𝗜𝚺₁) ∧ ComputableMarket x3History ∧
      ¬ ExactNNUAtInterval (quoteAt 𝗜𝚺₁) x3Cells x3History 1 x3Atom ∧
      ¬ (((0 : ℚ) : ℝ) * x3History 1 x3CellLo < x3History 1 x3Conj ∧
          x3History 1 x3Conj ≤ ((1 / 2 : ℚ) : ℝ) * x3History 1 x3CellLo) ∧
      ¬ ExactReflectionInterval (quoteAt 𝗜𝚺₁) x3Cells x3History ∧
      ¬ ExactNNUAt (quoteAt 𝗜𝚺₁) x3Cells x3History 1 x3Atom ∧
      ¬ ExactSelfTrustX (quoteAt 𝗜𝚺₁) x3Cells x3History :=
  ⟨x3_isLogicalInductor, x3_computableMarket, x3_not_exactNNUAtInterval, x3_interval_violation,
    x3_not_exactReflectionInterval, x3_not_exactNNUAt, x3_not_exactSelfTrustX⟩

/-- **What inhabits the predicates X3 refutes, at FAF's quote family**: Soto's two-clause bundle
market over X3's two-cell family with cell masses `½` satisfies the exact self-trust identity at
every `n < m`, every `φ` and both cells, with positive cell masses, **and** exact no-net-update at
`φ₀` on day 1, pricing `φ₀` at `∑ mid·½ = ⅛ + ⅜ = ½` (the conjunction masses are `¼·½` and `¾·½`).
Grade **N−** (repair round 2, audit r2 fidelity B1 / adversarial B2): it is a by-definition
valuation, `⊤`-incoherent at both cells (`sotoBundle_top_incoherent`: `P(⊤ ⋏ χ₀) = ⅛ ≠ ½ = P(χ₀)`),
and `coherentTop_forces_zero` shows no positive-mass inhabitant of the midpoint predicate can do
better. What it establishes: the midpoint predicates do not collapse to the zero history, and the
two identities are jointly satisfiable with positive masses — repair round 1's one-clause
inhabitant violated `ExactNNUAt` here (`¼·½ + ¾·½ = ½ ≠ 0`, audit r2 fidelity B1). The former
pointer to `bli-exact-base`'s `Bundle.BundleMarket` remains withdrawn.
Source: Soto PDF 20 p. 1–2 ([[bli-soto-b-inventory]] 025); mandate X6 (v); audit r2 fidelity
B1 (i), adversarial B2 (ii)
Kind: N-
Fidelity: n/a
Hyps: (a) -/
theorem sotoBundle_x3Cells_witness :
    ExactSelfTrustX (quoteAt 𝗜𝚺₁) x3Cells
        (sotoBundleHistory (quoteAt 𝗜𝚺₁) x3Cells (fun _ => (1 / 2 : ℝ))) ∧
      (∀ (n m : ℕ) (φ : Sentence), n < m → ∀ I ∈ x3Cells m,
        0 < sotoBundleHistory (quoteAt 𝗜𝚺₁) x3Cells (fun _ => (1 / 2 : ℝ)) n
          (quoteAt 𝗜𝚺₁ m φ I.1 I.2)) ∧
      ExactNNUAt (quoteAt 𝗜𝚺₁) x3Cells
        (sotoBundleHistory (quoteAt 𝗜𝚺₁) x3Cells (fun _ => (1 / 2 : ℝ))) 1 x3Atom ∧
      sotoBundleHistory (quoteAt 𝗜𝚺₁) x3Cells (fun _ => (1 / 2 : ℝ)) 1 x3Atom = 1 / 2 := by
  refine ⟨quoteAt_sotoBundle_exactSelfTrustX 𝗜𝚺₁ x3Cells _, fun n m φ hnm I hI => ?_,
    quoteAt_sotoBundle_exactNNUAt_of_not_isAnd 𝗜𝚺₁ x3Cells _ 1 (isAnd_atom 1), ?_⟩
  · rw [sotoBundle_quote (quoteAt_cellInjective 𝗜𝚺₁ x3Cells) _ hnm φ hI]
    norm_num
  · show sotoBundleHistory (quoteAt 𝗜𝚺₁) x3Cells (fun _ => (1 / 2 : ℝ)) 1 (Formula.atom 1) = 1 / 2
    rw [sotoBundle_obj _ 1 (objectLevel_quoteAt_atom 𝗜𝚺₁ 1)]
    have hne : ((0 : ℚ), (1 / 2 : ℚ)) ≠ (1 / 2, 1) := by norm_num
    show ∑ I ∈ ({(0, 1 / 2), (1 / 2, 1)} : Finset (ℚ × ℚ)), ((mid I : ℚ) : ℝ) * (1 / 2 : ℝ) = 1 / 2
    rw [Finset.sum_pair hne]
    norm_num [mid]

end Cleanroom.Bli.BliExactness
