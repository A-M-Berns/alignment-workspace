import Cleanroom.Bli.BliExactness.Abstract
import Cleanroom.Bli.BliFound.StateSentence
import Cleanroom.Bli.BliTrajectory.Defs
import LogicalInduction.Construction.Paper.Market

/-!
# `bli-exactness` — X1 (b)–(d) and X2 (ii)–(iii): the liar over FAF's diagonal

**Construction-facing module** (imports `Construction.Paper.Market`). The liar of record is FAF's
public diagonal atom for the single market at threshold `p`,
`liar T p m := (paperDiagonalQuoteCode T p).toBooleanQuoteCode.sentence m` — in every
completed-theory world of `paperDP T` it holds iff the market's own day-`m` price of it is below
`p` (`liar_reflected`). Precedent: `bli-linkage` angle B (`Cleanroom/Bli/BliLinkageB/FaithB2.lean`,
`liar`, `liar_reflected`, `liar_notMem_Sminus`) — copied, not imported (Known issue 10).

* **X1 (b)** `exact_reflection_fails_liar`: for every history `P`, every day `n`, every one-sided
  cell `(lo, hi]` (entirely below or entirely at-or-above `p`) of positive `P_n`-mass, if `P_n`
  respects the two entailments between the liar and the cell over the completed theory, **the
  conditional probability of the liar given the cell lies outside the cell**
  (`¬ (lo · P_n(χ) < P_n(L ⋏ χ) ≤ hi · P_n(χ))`): it is `1` below `p` and `0` at or above
  (`liar_cell_conditional`, slide 40's two cases). This is `exact_reflection_fails_abstract`
  with its (c) hypotheses **discharged at grade (a)** by `entailsIn_liarCell_liar` /
  `entailsIn_liarCell_notLiar` (from `le_of_holds_quoteAt` + `liar_reflected`). The midpoint
  form `P_n(L ⋏ χ) ≠ mid · P_n(χ)` is the corollary `exact_reflection_fails_liar_mid`.
* **Not a strengthening** (audit r1, both lenses): `liar_midpoint_fails_any_cell` — midpoint-
  exactness fails at **every** cell with `0 < mid < 1`, straddling or not, because the completed
  theory decides the liar (`liar_decided`). This is the F5 artifact: under theory-respect every
  decided sentence, `⊤` included, has conditional `0` or `1` (`Defs.lean`
  `decided_fails_midpoint`, `top_fails_midpoint`), so it carries no self-reference. Its witness
  `liar_cell_witness` is N− for the same reason. The interval claim, by contrast, is one `⊤`
  fails to satisfy at a cell reaching `1` (`top_exact_interval`) and the liar fails at every
  one-sided cell; it does **not** extend to straddling cells (at `(lo, 1]` with `lo < q < p` the
  liar's conditional `1` lies inside).
* **N+ of record for X1 (b)**: `liar_oneSided_witness_of_ne` — when `q := 𝑸_m(L) ≠ p`, a
  completed-theory world holds a one-sided cell, the point-mass history inhabits the full
  package, the liar's conditional falls outside the cell, and **a decided sentence of the
  opposite truth value is exactly reflected at the same cell by the same history** (`∼⊤` below,
  `⊤` above). **Register** (audit r2, both lenses): the separation is from the decided sentence
  of the *opposite* truth value only; at the one positive-mass cell a point mass has, the liar
  fails identically to the decided sentence of the *same* truth value (`⊤` at the below cell,
  `Defs.lean` `top_fails_below_cell`; `∼⊤` at the above cell), and both branch cells stick out
  of `[0, 1]` (`lo = q − 1 < 0`, `hi = q + 1 ≥ 1`), which is what lets `∼⊤`/`⊤` be interval-exact
  at them (findings F6: inside `[0, 1]` no `(lo, hi]` cell contains `0`). The liar-specific
  content below the threshold is `liar_cell_conditional`'s *direction* (certainty where `∼⊤`
  gives `0`); above it the separation is genuine inside `[0, 1]`. The condition `q ≠ p` is
  intrinsic (F6: no one-sided cell contains the threshold). Every inhabitant of the
  theory-respect hypothesis is `{0, P_n(χ)}`-valued on `L ⋏ χ` (`liar_decided`), so a point
  mass is representative, not a degenerate choice; the grade N+ stands on the above branch.
* `pointWorld_not_exactReflection`: no completed-theory point mass inhabits `ExactReflection`
  at `quoteAt T` on a family with a cell around `𝑸_m(⊤)` of midpoint `< 1` — the completed-theory
  instance of `Defs.lean` `coherentTop_forces_zero` (repair round 2): the midpoint predicate over
  every sentence has **no** `⊤`-coherent inhabitant with positive mass on such a cell, so X1's
  witnesses are never on a satisfiable side that a coherent market could occupy.
* **X1 (c)** artifact checks: `lia_liar_asymptotic` (`thm:lp`: the LIA prices its liar
  asymptotically at `p`); `lic_introspection_closed` is the surviving interval form (cited).
* **X1 (d)** `tierA_liar`/`bliHistory_liar` (B1 prices the liar by its base: a quotation atom
  is never a state atom), `liar_notMem_Sminus` (K4b re-proved: `E2x` never asks faith at the
  liar); (d3) restoration is **proved conditional** on `hQ : ComputableMarket (bliHistory …)`
  (`Open.lean`, same-day form; no open statement).
* **X2 (ii)** `lia_never_exact_on_liar`: the LIA's price of its own liar differs from the liar's
  truth value in every completed-theory world, on every day (so no day-`n` valuation that is
  both the market and exactly right about the liar exists); the abstract core is
  `no_sharp_fixed_point`. **X2 (iii)**: the surviving forms are `lia_liar_asymptotic` and
  FAF's `lic_introspection_closed`. **X2 (iv)**: `bli-exact-base`'s `Obstruction.obstruction`
  is a different constraint (its docstring says so); cited, not duplicated.

Theory parameters: `(T) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [LO.Entailment.Consistent T]` for the liar and the
reflection (as `Market.lean`'s `PeanoMinus` section), `[𝗥₀ ⪯ T]` where `quoteAt` is used, and
`[𝗜𝚺₁ ⪯ T]` only for the asymptotic artifact check (Known issue 7).
-/

namespace Cleanroom.Bli.BliExactness

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound Cleanroom.Bli.BliTrajectory

section Liar

variable (T : LO.FirstOrder.ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T]

/-- **The liar of record**: FAF's public diagonal atom for the single market at threshold `p`,
"my own day-`m` price is below `p`" (slide 40: `L := ℙ_m(L) < ½` at `p = ½`).
Source: slide 40 ([[bli-slides-inventory]] 041); FAF `paperDiagonalQuoteCode`
(`Construction/Paper/Market.lean:89`); precedent `bli-linkage` B `liar`
Kind: D
Fidelity: exact -/
noncomputable def liar (p : ℚ) (m : ℕ) : Sentence :=
  (paperDiagonalQuoteCode T p).toBooleanQuoteCode.sentence m

/-- The liar is the quotation atom at `⟨code, m⟩`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma liar_eq (p : ℚ) (m : ℕ) :
    liar T p m = quoteAtom (Nat.pair (paperDiagonalQuoteCode T p).code m) := rfl

/-- **The liar's reflection**: in every completed-theory world of `paperDP T`, `liar T p m` holds
iff the market's day-`m` price of it is below `p`.
Source: FAF `BooleanQuoteCode.reflected` at `paperQuotationPresentation`; `diagonalPriceTruth`;
precedent `bli-linkage` B `liar_reflected`
Kind: L (FAF one-liner; regraded from C in repair r1)
Fidelity: exact
Hyps: (a) -/
theorem liar_reflected (p : ℚ) (m : ℕ) (v : PCWorld) (hv : v.ConsistentWithTheory (paperDP T)) :
    v.Holds (liar T p m) ↔ paperQuote T m (Encodable.encode (liar T p m)) < p :=
  (paperDiagonalQuoteCode T p).toBooleanQuoteCode.reflected (paperQuotationPresentation T) m v hv

/-- The liar's price lies in `[0, 1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma liar_price_mem (p : ℚ) (m : ℕ) :
    0 ≤ paperQuote T m (Encodable.encode (liar T p m)) ∧
      paperQuote T m (Encodable.encode (liar T p m)) ≤ 1 :=
  paperQuote_mem T m _

/-- **The completed theory decides the liar**: every completed-theory world holds it, or every one
refutes it — its truth is the fixed rational fact `𝑸_m(L) < p` about the market's own price. This
is what makes the *midpoint* identity fail at every cell with interior midpoint
(`liar_midpoint_fails_any_cell`) — the F5 artifact, shared by every decided sentence
(`Defs.lean` `decided_fails_midpoint`); it does **not** void the slide's straddling caveat for the
interval claim (repair round 1).
Source: FAF `BooleanQuoteCode.reflected` (the truth predicate is world-independent)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem liar_decided (p : ℚ) (m : ℕ) :
    (∀ v : PCWorld, v.ConsistentWithTheory (paperDP T) → v.Holds (liar T p m)) ∨
    (∀ v : PCWorld, v.ConsistentWithTheory (paperDP T) → ¬ v.Holds (liar T p m)) := by
  by_cases h : paperQuote T m (Encodable.encode (liar T p m)) < p
  · exact Or.inl fun v hv => (liar_reflected T p m v hv).2 h
  · exact Or.inr fun v hv hL => h ((liar_reflected T p m v hv).1 hL)

/-- Hence the liar entails, or is refuted by, every sentence over the completed theory.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem entailsIn_liar_or_notLiar (p : ℚ) (m : ℕ) (ψ : Sentence) :
    EntailsIn (TheoryWorlds (paperDP T)) ψ (liar T p m) ∨
      EntailsIn (TheoryWorlds (paperDP T)) ψ (∼ liar T p m) := by
  rcases liar_decided T p m with h | h
  · exact Or.inl fun v hv _ => h v hv
  · exact Or.inr fun v hv _ => (PCWorld.holds_neg v _).2 (h v hv)

/-- **K4b re-proved — the scope lemma**: the liar of day `m` lies in no `Sminus n m` (its packed
input is `⟨code, m⟩`, read by `atomDay` as `m`), so `bli-found`'s `E2x` (scope `Sminus m m`) never
asks for faith at the liar: B1's constraint 2 escapes the liar by its scope (X1 (d2)).
Source: [[bli-program]] §3.6 (iv); precedent `bli-linkage` B `liar_notMem_Sminus`; mandate X1 (d2)
Kind: L
Fidelity: exact (for the scope of record)
Hyps: (a) -/
theorem liar_notMem_Sminus (p : ℚ) (m n : ℕ) : liar T p m ∉ Sminus n m := by
  intro h
  rw [mem_Sminus] at h
  have := h.2 (quotationClaimCode universalQuotePos universalQuoteNeg
    (Nat.pair (paperDiagonalQuoteCode T p).code m))
    (by simp [liar_eq, quoteAtom, quotationClaimSentence])
  rw [atomDay_quotationClaimCode, Nat.unpair_pair] at this
  exact lt_irrefl _ this

end Liar

/-! ## X1 (d1): B1 prices the liar by its base -/

section TierA

variable (T : LO.FirstOrder.ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T]

/-- A quotation atom carries tag `2`, never the state tag: `stateData` reads nothing off it.
Source: `bli-found` `freshAtom_ne_quoteAtom` (tag disjointness)
Kind: L
Fidelity: n/a -/
lemma stateData_quoteAtom (w : ℕ) :
    stateData (quotationClaimCode universalQuotePos universalQuoteNeg w) = none := by
  unfold stateData
  rw [if_neg]
  simp [quotationClaimCode, Nat.unpair_pair, stateTag, cleanroomBaseTag]

/-- **The liar is Tier B for every state coding**: `tierA c n (liar T p m) = none` — a quotation
atom is never a state atom (`stateData_quoteAtom`), so its parse has an empty chain.
Source: mandate X1 (d1); `bli-trajectory` `tierA`
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem tierA_liar {𝓜 : BliFinite.Mesh} (c : StateCoding 𝓜) (n : ℕ) (p : ℚ) (m : ℕ) :
    tierA c n (liar T p m) = none := by
  rw [liar_eq, quoteAtom, quotationClaimSentence]
  simp [tierA, parse, futureStateAtom, stateData_quoteAtom]

/-- **B1 prices the liar by its base**: `bliHistory Q 𝓜 sk c n (liar T p m) = Q n (liar T p m)` for
every state coding, skeleton and base. The liar never enters Tier A, so constraint 2's machinery
is silent on it on both sides (`liar_notMem_Sminus` for the scope, this for the price).
Source: mandate X1 (d1); [[bli-program]] §2.5
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem bliHistory_liar (Q : BliFinite.RatHistory) (𝓜 : BliFinite.Mesh)
    (sk : BliFinite.Skeleton smallIndex 𝓜.d) (c : StateCoding 𝓜) (n : ℕ) (p : ℚ) (m : ℕ) :
    bliHistory Q 𝓜 sk c n (liar T p m) = ((Q n (liar T p m) : ℚ) : ℝ) := by
  unfold bliHistory bliPrice
  rw [tierA_liar]
  split_ifs <;> rfl

end TierA

/-! ## X1 (b): exact reflection fails on the liar's own cells -/

section Cells

variable (T : LO.FirstOrder.ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [𝗥₀ ⪯ T]

/-- **The liar's own cell**: `bli-found`'s interval quote "`lo < 𝑸_m(liar) ≤ hi`" about the paper
market's day-`m` price of the liar — the partition event "`ℙ_m(L) = p`" at interval resolution.
Source: slide 40 (the partition events); `bli-found` `quoteAt`
Kind: D
Fidelity: exact -/
noncomputable abbrev liarCell (p : ℚ) (m : ℕ) (lo hi : ℚ) : Sentence :=
  quoteAt T m (liar T p m) lo hi

/-- A cell entirely below the threshold entails the liar over the completed theory
(`hi < p`: a world holding the cell has `𝑸_m(L) ≤ hi < p`, so `L`).
Source: mandate X1 (b) (the two lemmas); `le_of_holds_quoteAt` + `liar_reflected`
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem entailsIn_liarCell_liar {p : ℚ} {m : ℕ} {lo hi : ℚ} (hhi : hi < p) :
    EntailsIn (TheoryWorlds (paperDP T)) (liarCell T p m lo hi) (liar T p m) := by
  intro v hv hχ
  have h := le_of_holds_quoteAt T v hv hχ
  exact (liar_reflected T p m v hv).2 (lt_of_le_of_lt h.2 hhi)

/-- A cell entirely at or above the threshold entails the liar's negation
(`p ≤ lo`: a world holding the cell has `𝑸_m(L) ≥ lo ≥ p`, so `∼L`).
Source: mandate X1 (b)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem entailsIn_liarCell_notLiar {p : ℚ} {m : ℕ} {lo hi : ℚ} (hlo : p ≤ lo) :
    EntailsIn (TheoryWorlds (paperDP T)) (liarCell T p m lo hi) (∼ liar T p m) := by
  intro v hv hχ
  have h := le_of_holds_quoteAt T v hv hχ
  rw [PCWorld.holds_neg, liar_reflected T p m v hv]
  exact not_lt.2 (le_trans hlo h.1)

/-- **Slide 40's two cases over FAF's diagonal**: if `P_n` respects the two entailments between
the liar and a cell over the completed theory, then on a cell entirely below `p` the liar is
certain given the cell (`P_n(L ⋏ χ) = P_n(χ)`) and on a cell entirely at or above `p` it is
impossible given the cell (`P_n(L ⋏ χ) = 0`). This is the content the interval and midpoint
theorems below are arithmetic consequences of; the direction of each case is the liar's
anti-correlation with its own price (`liar_reflected`), which `⊤` does not share.
Source: slide 40 bullet 2 ([[bli-slides-inventory]] 041); audit r1 adversarial B2 ("the honest
positive statement")
Kind: C
Fidelity: exact (interval resolution)
Hyps: (a) `hresp` -/
theorem liar_cell_conditional (p : ℚ) (P : History) (n m : ℕ) {lo hi : ℚ}
    (hresp : RespectsEntailment (TheoryWorlds (paperDP T)) (P n) (liar T p m)
      (liarCell T p m lo hi)) :
    (hi < p → P n (liar T p m ⋏ liarCell T p m lo hi) = P n (liarCell T p m lo hi)) ∧
    (p ≤ lo → P n (liar T p m ⋏ liarCell T p m lo hi) = 0) :=
  ⟨fun h => hresp.1 (entailsIn_liarCell_liar T h), fun h => hresp.2 (entailsIn_liarCell_notLiar T h)⟩

/-- **X1 (b) — exact reflection fails on FAF's liar, one-sided cells, interval form** (slide 40
bullet 2 over the real diagonal). For every history `P`, every day `n`, every threshold
`p ∈ (0, 1]`, every one-sided cell `(lo, hi]` (`hi < p` or `p ≤ lo`) of positive `P_n`-mass: if
`P_n` respects the two entailments between the liar and the cell over the completed theory of
`paperDP T`, then **the conditional probability of the liar given the cell lies outside the cell**:
`¬ (lo · P_n(χ) < P_n(L ⋏ χ) ≤ hi · P_n(χ))` with `χ := ⌜𝑸_m(L) ∈ (lo, hi]⌝` — the conditional is
`1 > hi` below and `0 ≤ lo` at or above (`liar_cell_conditional`).
The abstract theorem's (c) hypotheses are discharged here at grade (a): the only hypothesis left
is theory-respect on this one pair of sentences. The day `n` is arbitrary (`n < m` is not needed;
at `n = m` this is the same-day form). Theory-respect is **relative to the completed theory**: the
day-`m` price is a fact of the completed theory, not of a stage `D n` with `n < m`; the
stage-relative variant is not claimed (report). For theory-respecting `P` the cells of positive
mass are those containing the quote `q` (otherwise both entailments hold vacuously and `hresp`
forces `P_n(χ) = 0`), so "every one-sided cell of positive mass" means the one-sided cells
containing `q` — which exist iff `q ≠ p` (findings F6).
Source: slide 40 bullet 2 ([[bli-slides-inventory]] 041); mandate X1 (b), judged item 1;
audit r1 fidelity B1 (interval conclusion adopted)
Kind: C
Fidelity: exact (interval resolution; one-sided cells; completed-theory respect)
Hyps: (a) `hresp`: respect for the **completed** theory on the pair `(L, χ)` — the stage-relative
variant is not claimed; inhabited by every world mixture (`mixture_respectsEntailment`);
(a) `hpos` -/
theorem exact_reflection_fails_liar {p : ℚ} (hp₀ : 0 < p) (hp₁ : p ≤ 1) (P : History)
    (n m : ℕ) {lo hi : ℚ} (hside : hi < p ∨ p ≤ lo)
    (hresp : RespectsEntailment (TheoryWorlds (paperDP T)) (P n) (liar T p m)
      (liarCell T p m lo hi))
    (hpos : 0 < P n (liarCell T p m lo hi)) :
    ¬ ((lo : ℝ) * P n (liarCell T p m lo hi) < P n (liar T p m ⋏ liarCell T p m lo hi) ∧
        P n (liar T p m ⋏ liarCell T p m lo hi) ≤ (hi : ℝ) * P n (liarCell T p m lo hi)) :=
  exact_reflection_fails_abstract (ι := Unit) (liar T p m) (fun _ => liarCell T p m lo hi)
    (fun _ => (lo, hi)) (· ⋏ ·) (P n) p hp₀ hp₁
    (fun _ h => hresp.1 (entailsIn_liarCell_liar T h))
    (fun _ h => hresp.2 (entailsIn_liarCell_notLiar T h))
    () hside hpos

/-- **X1 (b), midpoint form**: under the same hypotheses, at a one-sided cell with `lo ≤ hi`,
`P_n(L ⋏ χ) ≠ mid(lo, hi) · P_n(χ)`. The weaker, F5 reading of the interval theorem (the shape the
refutations of `ExactReflection` instantiate).
Source: slide 40 bullet 2; mandate X1 (b); findings F5
Kind: C
Fidelity: weaker: midpoint representative in place of the interval conclusion
Hyps: (a) as `exact_reflection_fails_liar` -/
theorem exact_reflection_fails_liar_mid {p : ℚ} (hp₀ : 0 < p) (hp₁ : p ≤ 1) (P : History)
    (n m : ℕ) {lo hi : ℚ} (hI : lo ≤ hi) (hside : hi < p ∨ p ≤ lo)
    (hresp : RespectsEntailment (TheoryWorlds (paperDP T)) (P n) (liar T p m)
      (liarCell T p m lo hi))
    (hpos : 0 < P n (liarCell T p m lo hi)) :
    P n (liar T p m ⋏ liarCell T p m lo hi) ≠
      ((mid (lo, hi) : ℚ) : ℝ) * P n (liarCell T p m lo hi) :=
  exact_reflection_fails_abstract_mid (ι := Unit) (liar T p m) (fun _ => liarCell T p m lo hi)
    (fun _ => (lo, hi)) (· ⋏ ·) (P n) p hp₀ hp₁
    (fun _ h => hresp.1 (entailsIn_liarCell_liar T h))
    (fun _ h => hresp.2 (entailsIn_liarCell_notLiar T h))
    () hI hside hpos

/-- **The F5 artifact at the liar — not a strengthening of X1 (b)** (formerly
`exact_reflection_fails_liar_cell`, "the FAF strengthening"; demoted in repair round 1). For
every cell `(lo, hi]` with `0 < mid < 1` and positive `P_n`-mass, theory-respect on the pair forces
`P_n(L ⋏ χ) ∈ {P_n(χ), 0}` (the completed theory decides the liar, `liar_decided`), neither of
which is `mid · P_n(χ)`. The same statement holds with **any** completed-theory-decided sentence
in place of the liar — `⊤` included (`Defs.lean` `decided_fails_midpoint`, `top_fails_midpoint`):
what fails here is midpoint-exactness for a sentence whose truth value is known, not reflection
about a self-referential price. The slide's straddling caveat is therefore void over FAF only
for the midpoint reading; the interval claim does not extend to straddling cells.
Source: findings F5; audit r1 fidelity B1 / adversarial B2
Kind: L
Fidelity: n/a — instance of `decided_fails_midpoint` at the liar (the midpoint artifact)
Hyps: (a) `hresp`, `hpos`, `hmid` -/
theorem liar_midpoint_fails_any_cell (p : ℚ) (P : History) (n m : ℕ) {lo hi : ℚ}
    (hmid₀ : 0 < mid (lo, hi)) (hmid₁ : mid (lo, hi) < 1)
    (hresp : RespectsEntailment (TheoryWorlds (paperDP T)) (P n) (liar T p m)
      (liarCell T p m lo hi))
    (hpos : 0 < P n (liarCell T p m lo hi)) :
    P n (liar T p m ⋏ liarCell T p m lo hi) ≠
      ((mid (lo, hi) : ℚ) : ℝ) * P n (liarCell T p m lo hi) :=
  decided_fails_midpoint (TheoryWorlds (paperDP T)) (liar T p m) (liarCell T p m lo hi) (P n)
    (liar_decided T p m) hmid₀ hmid₁ hresp hpos

/-- **Corollary: no theory-respecting history with positive mass on a one-sided cell of the family
is exactly reflective on that family** — if some day `n < m` and some one-sided cell
`(lo, hi] ∈ cells m` with `lo ≤ hi` has positive mass and theory-respect at the liar, then
`¬ ExactReflection (quoteAt T) cells P`. (The predicate's refutation at a *straddling* cell of the
family would go through `liar_midpoint_fails_any_cell` and is the F5 artifact; it is not stated.)
Source: mandate X1 (b) (corollary); slide 40 bullet 2
Kind: L
Fidelity: exact (family-relative)
Hyps: (a) as `exact_reflection_fails_liar` -/
theorem not_exactReflection_of_liar {p : ℚ} (hp₀ : 0 < p) (hp₁ : p ≤ 1) (P : History)
    (cells : ℕ → Finset (ℚ × ℚ)) {n m : ℕ} (hnm : n < m) {lo hi : ℚ} (hcell : (lo, hi) ∈ cells m)
    (hI : lo ≤ hi) (hside : hi < p ∨ p ≤ lo)
    (hresp : RespectsEntailment (TheoryWorlds (paperDP T)) (P n) (liar T p m)
      (liarCell T p m lo hi))
    (hpos : 0 < P n (liarCell T p m lo hi)) :
    ¬ ExactReflection (quoteAt T) cells P :=
  fun h => exact_reflection_fails_liar_mid T hp₀ hp₁ P n m hI hside hresp hpos
    (h n m hnm (liar T p m) (lo, hi) hcell)

/-! ### Witnesses: one completed-theory world -/

omit [𝗣𝗔⁻ ⪯ T] in
/-- **No completed-theory point mass inhabits `ExactReflection`** at `bli-found`'s `quoteAt T`:
if the family has, on some day `m > n`, a cell `(lo, hi)` strictly around the paper quote
`q := 𝑸_m(⊤)` with `mid < 1`, then `pointWorldHistory v` violates the identity at `φ := ⊤` —
the world holds the cell, holds `⊤ ⋏ χ`, and `1 = mid · 1` is false. So X1's witnesses are
witnesses of the per-cell failure only and never of the predicate's satisfiable side. This is the
completed-theory instance of `Defs.lean` `coherentTop_forces_zero` (repair round 2): coherence at
`⊤` alone does it, the quote plays no role, and the predicate over every sentence has no
`⊤`-coherent inhabitant with positive mass on a cell of midpoint `≠ 1` — its inhabitants
(`sotoBundleHistory`) are `⊤`-incoherent by necessity. A world *mixture* with positive total mass
fails the same way (all completed-theory worlds agree on `q`); not separately stated.
Source: audit r1 fidelity B2 (v); audit r2 adversarial B2
Kind: L
Fidelity: n/a -/
theorem pointWorld_not_exactReflection (cells : ℕ → Finset (ℚ × ℚ)) {n m : ℕ} (hnm : n < m)
    {lo hi : ℚ} (hcell : (lo, hi) ∈ cells m)
    (hlo : lo < paperQuote T m (Encodable.encode (⊤ : Sentence)))
    (hhi : paperQuote T m (Encodable.encode (⊤ : Sentence)) < hi) (hmid : mid (lo, hi) < 1)
    (v : PCWorld) (hv : v.ConsistentWithTheory (paperDP T)) :
    ¬ ExactReflection (quoteAt T) cells (pointWorldHistory v) := by
  intro h
  have hid := h n m hnm ⊤ (lo, hi) hcell
  have hχ : v.Holds (quoteAt T m ⊤ lo hi) := holds_quoteAt_of_lt_of_lt T hlo hhi v hv
  have hand : v.Holds ((⊤ : Sentence) ⋏ quoteAt T m ⊤ lo hi) :=
    (PCWorld.holds_and v _ _).2 ⟨PCWorld.holds_top v, hχ⟩
  simp only [pointWorldHistory_apply, PCWorld.payout, if_pos hχ, if_pos hand, mul_one] at hid
  have hmidR : ((mid (lo, hi) : ℚ) : ℝ) < 1 := by exact_mod_cast hmid
  linarith

omit [𝗥₀ ⪯ T] in
/-- There is a completed-theory world of `paperDP T` (compactness from `paperDP_hworld`).
Source: FAF `DeductiveProcess.exists_consistentWithTheory`, `paperDP_hworld`
Kind: L
Fidelity: n/a -/
theorem exists_theoryWorld [LO.Entailment.Consistent T] :
    ∃ v : PCWorld, v.ConsistentWithTheory (paperDP T) :=
  (paperDP T).exists_consistentWithTheory (paperDP_hworld T)

/-- **Witness of the F5 artifact (N−)** — formerly graded N+ "for `exact_reflection_fails_liar_cell`,
unconditional". For every threshold `p` and day `m`, a completed-theory world `v` and a cell
`((q−1)/2, (q+2)/2]` around the actual quote `q = 𝑸_m(L)` (midpoint `(2q+1)/4 ∈ [¼, ¾]`, held by
`v`; the cell contains all of `[0, 1]`) such that the point-mass history inhabits the full
hypothesis package of `liar_midpoint_fails_any_cell` and the midpoint identity fails.
**Why N−** (audit r1, both lenses): the same scheme inhabits the same package with *any*
sentence in place of the liar and exhibits the same failure — a `{0, 1}`-valued valuation has no
fractional conditional; the liar plays no role (`Defs.lean` `top_fails_midpoint`). Kept because
the theorem it witnesses is kept (as the artifact it is). The N+ of record for X1 (b) is
`liar_oneSided_witness_of_ne`.
Source: mandate X1 (b) (N+ — regraded); audit r1 fidelity B1 (iii), adversarial B2
Kind: N-
Fidelity: n/a
Hyps: (a) -/
theorem liar_cell_witness [LO.Entailment.Consistent T] (p : ℚ) (m : ℕ) :
    ∃ (v : PCWorld) (lo hi : ℚ), v.ConsistentWithTheory (paperDP T) ∧
      0 < mid (lo, hi) ∧ mid (lo, hi) < 1 ∧
      0 < pointWorldHistory v 0 (liarCell T p m lo hi) ∧
      RespectsEntailment (TheoryWorlds (paperDP T)) (pointWorldHistory v 0) (liar T p m)
        (liarCell T p m lo hi) ∧
      pointWorldHistory v 0 (liar T p m ⋏ liarCell T p m lo hi) ≠
        ((mid (lo, hi) : ℚ) : ℝ) * pointWorldHistory v 0 (liarCell T p m lo hi) := by
  obtain ⟨v, hv⟩ := exists_theoryWorld T
  set q := paperQuote T m (Encodable.encode (liar T p m)) with hq
  obtain ⟨hq0, hq1⟩ := liar_price_mem T p m
  have hmid₀ : 0 < mid ((q - 1) / 2, (q + 2) / 2) := by simp only [mid]; linarith
  have hmid₁ : mid ((q - 1) / 2, (q + 2) / 2) < 1 := by simp only [mid]; linarith
  have hholds : v.Holds (liarCell T p m ((q - 1) / 2) ((q + 2) / 2)) :=
    holds_quoteAt_of_lt_of_lt T (by linarith) (by linarith) v hv
  have hpos : 0 < pointWorldHistory v 0 (liarCell T p m ((q - 1) / 2) ((q + 2) / 2)) := by
    rw [pointWorldHistory_apply, PCWorld.payout, if_pos hholds]; norm_num
  have hresp : RespectsEntailment (TheoryWorlds (paperDP T)) (pointWorldHistory v 0)
      (liar T p m) (liarCell T p m ((q - 1) / 2) ((q + 2) / 2)) :=
    payout_respectsEntailment (𝒲 := TheoryWorlds (paperDP T)) hv _ _
  exact ⟨v, (q - 1) / 2, (q + 2) / 2, hv, hmid₀, hmid₁, hpos, hresp,
    liar_midpoint_fails_any_cell T p (pointWorldHistory v) 0 m hmid₀ hmid₁ hresp hpos⟩

/-- **N+ of record for X1 (b)** (`exact_reflection_fails_liar`, one-sided cells), when the quote
is off the threshold: if `q := 𝑸_m(L) ≠ p`, a completed-theory world holds a one-sided cell —
below (`(q−1, (q+p)/2]`) when `q < p`, above (`(p, q+1]`) when `q > p` — the point-mass history
inhabits the full package, the liar's conditional lies outside the cell, **and a decided sentence
of the opposite truth value is exactly reflected at the same cell by the same history**: `∼⊤`
below (conditional `0 ∈ (q−1, (q+p)/2]`), `⊤` above (conditional `1 ∈ (p, q+1]`). So the failure
exhibited is that of a sentence whose truth value is anti-correlated with its own price, and not
the `{0,1}`-valuedness of a point mass as such (audit r1 adversarial B2: every inhabitant of the
theory-respect hypothesis is `{0, P(χ)}`-valued on `L ⋏ χ` by `liar_decided`, so a point mass is
representative; the separating conjunct is what makes the grade N+ rather than N−). **Register,
corrected in repair round 2** (audit r2 fidelity N1, adversarial N1): the separation is from the
decided sentence of the *opposite* truth value only. At the chosen cell the liar fails exactly as
the decided sentence of the *same* truth value does — `⊤` at the below cell (`hi = (q+p)/2 < 1`,
`Defs.lean` `top_fails_below_cell`), `∼⊤` at the above cell (`lo = p > 0`) — and both branch cells
stick out of `[0, 1]` (`lo = q − 1 < 0`; `hi = q + 1 ≥ 1`), which is what lets `∼⊤` and `⊤` be
interval-exact at them (findings F6: inside `[0, 1]` no `(lo, hi]` cell contains `0`, so there no
false sentence is interval-exact anywhere and `⊤` only at the top cell). Below the threshold the
liar-specific content is therefore `liar_cell_conditional`'s *direction* — `P(L ⋏ χ) = P(χ)`,
certainty where `∼⊤` would give `0` — rather than the interval failure as such; above it the
separation from `∼⊤` is genuine inside `[0, 1]`. Nothing finer exists for this hypothesis package
(`liar_decided` pins one truth value per history, so one history exercises one branch). When `q = p`
exactly no one-sided `(lo, hi]` cell contains `q`, so no world mixture has positive mass on one
(findings F6) — the condition `hne` is intrinsic to one-sidedness, not to the failure.
Source: mandate X1 (b) (N+: "the cell chosen by cases on `paperQuote T m ⌜liar⌝ < ½`");
audit r1 fidelity B1 (iii), adversarial B2; audit r2 fidelity N1, adversarial N1
Kind: N+
Fidelity: n/a
Hyps: (a) `hp₀`, `hp₁`; (a) `hne` (the quote is not exactly the threshold; findings F6) -/
theorem liar_oneSided_witness_of_ne [LO.Entailment.Consistent T] {p : ℚ} (hp₀ : 0 < p)
    (hp₁ : p ≤ 1) (m : ℕ)
    (hne : paperQuote T m (Encodable.encode (liar T p m)) ≠ p) :
    ∃ (v : PCWorld) (lo hi : ℚ), v.ConsistentWithTheory (paperDP T) ∧
      lo ≤ hi ∧ (hi < p ∨ p ≤ lo) ∧
      0 < pointWorldHistory v 0 (liarCell T p m lo hi) ∧
      RespectsEntailment (TheoryWorlds (paperDP T)) (pointWorldHistory v 0) (liar T p m)
        (liarCell T p m lo hi) ∧
      ¬ ((lo : ℝ) * pointWorldHistory v 0 (liarCell T p m lo hi) <
            pointWorldHistory v 0 (liar T p m ⋏ liarCell T p m lo hi) ∧
          pointWorldHistory v 0 (liar T p m ⋏ liarCell T p m lo hi) ≤
            (hi : ℝ) * pointWorldHistory v 0 (liarCell T p m lo hi)) ∧
      ∃ ψ : Sentence,
        ((∀ u : PCWorld, u.Holds ψ) ∨ (∀ u : PCWorld, ¬ u.Holds ψ)) ∧
        (lo : ℝ) * pointWorldHistory v 0 (liarCell T p m lo hi) <
            pointWorldHistory v 0 (ψ ⋏ liarCell T p m lo hi) ∧
          pointWorldHistory v 0 (ψ ⋏ liarCell T p m lo hi) ≤
            (hi : ℝ) * pointWorldHistory v 0 (liarCell T p m lo hi) := by
  obtain ⟨v, hv⟩ := exists_theoryWorld T
  set q := paperQuote T m (Encodable.encode (liar T p m)) with hq
  obtain ⟨hq0, hq1⟩ := liar_price_mem T p m
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- below: cell `(q − 1, (q + p)/2]`; the separating sentence is `∼⊤` (conditional `0`)
    have hholds : v.Holds (liarCell T p m (q - 1) ((q + p) / 2)) :=
      holds_quoteAt_of_lt_of_lt T (by linarith) (by linarith) v hv
    have hpos : 0 < pointWorldHistory v 0 (liarCell T p m (q - 1) ((q + p) / 2)) := by
      rw [pointWorldHistory_apply, PCWorld.payout, if_pos hholds]; norm_num
    have hresp : RespectsEntailment (TheoryWorlds (paperDP T)) (pointWorldHistory v 0)
        (liar T p m) (liarCell T p m (q - 1) ((q + p) / 2)) :=
      payout_respectsEntailment (𝒲 := TheoryWorlds (paperDP T)) hv _ _
    have hI : q - 1 ≤ (q + p) / 2 := by linarith
    have hside : (q + p) / 2 < p ∨ p ≤ q - 1 := Or.inl (by linarith)
    refine ⟨v, q - 1, (q + p) / 2, hv, hI, hside, hpos, hresp,
      exact_reflection_fails_liar T hp₀ hp₁ (pointWorldHistory v) 0 m hside hresp hpos,
      ∼(⊤ : Sentence), Or.inr fun u hu => (PCWorld.holds_neg u _).1 hu (PCWorld.holds_top u), ?_⟩
    have hnot : ¬ v.Holds (∼(⊤ : Sentence) ⋏ liarCell T p m (q - 1) ((q + p) / 2)) := fun h =>
      (PCWorld.holds_neg v _).1 ((PCWorld.holds_and v _ _).1 h).1 (PCWorld.holds_top v)
    simp only [pointWorldHistory_apply, PCWorld.payout, if_pos hholds, if_neg hnot, mul_one]
    have h1 : ((q - 1 : ℚ) : ℝ) < 0 := by
      have : q - 1 < 0 := by linarith
      exact_mod_cast this
    have h2 : (0 : ℝ) ≤ (((q + p) / 2 : ℚ) : ℝ) := by
      have : 0 ≤ (q + p) / 2 := by linarith
      exact_mod_cast this
    exact ⟨h1, h2⟩
  · -- above: cell `(p, q + 1]`; the separating sentence is `⊤` (conditional `1`)
    have hholds : v.Holds (liarCell T p m p (q + 1)) :=
      holds_quoteAt_of_lt_of_lt T (by linarith) (by linarith) v hv
    have hpos : 0 < pointWorldHistory v 0 (liarCell T p m p (q + 1)) := by
      rw [pointWorldHistory_apply, PCWorld.payout, if_pos hholds]; norm_num
    have hresp : RespectsEntailment (TheoryWorlds (paperDP T)) (pointWorldHistory v 0)
        (liar T p m) (liarCell T p m p (q + 1)) :=
      payout_respectsEntailment (𝒲 := TheoryWorlds (paperDP T)) hv _ _
    have hI : p ≤ q + 1 := by linarith
    have hside : q + 1 < p ∨ p ≤ p := Or.inr le_rfl
    refine ⟨v, p, q + 1, hv, hI, hside, hpos, hresp,
      exact_reflection_fails_liar T hp₀ hp₁ (pointWorldHistory v) 0 m hside hresp hpos,
      (⊤ : Sentence), Or.inl fun u => PCWorld.holds_top u, ?_⟩
    have hand : v.Holds ((⊤ : Sentence) ⋏ liarCell T p m p (q + 1)) :=
      (PCWorld.holds_and v _ _).2 ⟨PCWorld.holds_top v, hholds⟩
    simp only [pointWorldHistory_apply, PCWorld.payout, if_pos hholds, if_pos hand, mul_one]
    have h1 : (p : ℝ) < 1 := by
      have : p < 1 := lt_of_lt_of_le hgt hq1
      exact_mod_cast this
    have h2 : (1 : ℝ) ≤ ((q + 1 : ℚ) : ℝ) := by
      have : (1 : ℚ) ≤ q + 1 := by linarith
      exact_mod_cast this
    exact ⟨h1, h2⟩

end Cells

/-! ## X2 (ii): the market is never exactly right about its own liar -/

section Introspection

variable (T : LO.FirstOrder.ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T]

/-- **X2 (ii) — the LIA's price of its own liar is never its truth value**: on every day `m` and
in every completed-theory world `v`, `liaHistory (paperDP T) m (liar T p m) ≠ v.payout (liar T p m)`
for `p ∈ (0, 1]`. The truth value is `𝟙(q < p)` with `q` the price itself (`liar_reflected`), and
`q = 𝟙(q < p)` has no solution (`no_sharp_fixed_point`). So a market that is *exactly*
introspective about its own liar atom — prices it at its truth value — does not exist; the
surviving forms are the asymptotic `lia_liar_asymptotic` (the price tends to `p`) and FAF's
`ε_n`-band `lic_introspection_closed`. Soto's syntactic point (bli-soto-a-058 (iii): the
self-referential sentence lacks its own numeral) is moot over FAF, whose `BooleanQuoteCode.sentence`
*is* an atom.
Source: Soto PDF 07 p. 4–5 ([[bli-soto-a-inventory]] 058 (ii)); PDF 04 p. 5 fn. 3 (036 (ii));
mandate X2 (ii)
Kind: C
Fidelity: exact (same-day, the market's own liar atom)
Hyps: (a) -/
theorem lia_never_exact_on_liar {p : ℚ} (hp₀ : 0 < p) (hp₁ : p ≤ 1) (m : ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory (paperDP T)) :
    liaHistory (paperDP T) m (liar T p m) ≠ v.payout (liar T p m) := by
  intro heq
  rw [paperQuote_eq_liaHistory] at heq
  have hpay : v.payout (liar T p m) =
      if paperQuote T m (Encodable.encode (liar T p m)) < p then 1 else 0 := by
    unfold PCWorld.payout
    rw [liar_reflected T p m v hv]
    split_ifs <;> rfl
  rw [hpay] at heq
  have hp₀R : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp₀
  have hp₁R : (p : ℝ) ≤ 1 := by exact_mod_cast hp₁
  refine no_sharp_fixed_point (p : ℝ) hp₀R hp₁R
    ⟨((paperQuote T m (Encodable.encode (liar T p m)) : ℚ) : ℝ), ?_⟩
  by_cases h : paperQuote T m (Encodable.encode (liar T p m)) < p
  · have h' : ((paperQuote T m (Encodable.encode (liar T p m)) : ℚ) : ℝ) < (p : ℝ) := by
      exact_mod_cast h
    rw [if_pos h] at heq; rw [if_pos h']; exact heq
  · have h' : ¬ ((paperQuote T m (Encodable.encode (liar T p m)) : ℚ) : ℝ) < (p : ℝ) := by
      exact_mod_cast h
    rw [if_neg h] at heq; rw [if_neg h']; exact heq

/-- The sharp fixed-point reading at any history: no `Q` prices the liar at `𝟙(Q_m(L) < p)`
(pure arithmetic, recorded for the ledger's X2 (ii) row as the "`ExactIntro` read at the liar's
own atom" form the mandate names).
Source: mandate X2 (ii)
Kind: L
Fidelity: n/a -/
theorem no_history_sharp_at_liar {p : ℚ} (hp₀ : 0 < p) (hp₁ : p ≤ 1) (Q : History) (m : ℕ) :
    Q m (liar T p m) ≠ if Q m (liar T p m) < (p : ℝ) then 1 else 0 :=
  fun h => no_sharp_fixed_point (p : ℝ) (by exact_mod_cast hp₀) (by exact_mod_cast hp₁) ⟨_, h⟩

end Introspection

/-! ## X1 (c) / X2 (iii): the surviving asymptotic form -/

section Asymptotic

variable (T : LO.FirstOrder.ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] [LO.Entailment.Consistent T]

/-- **Artifact check**: the LIA prices its liar asymptotically at `p` — the continuous/asymptotic
form of the refuted exact identity is satisfied by an actual inductor (`thm:lp`). So the
impossibility in X1/X2 is the *exactness*, not the self-reference.
Source: FAF `lic_paradox_resistance_ofDiagonal_unconditional` (`Construction/Paper/Market.lean:657`);
mandate X1 (c), X2 (iii)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem lia_liar_asymptotic (p : ℚ) (hp₀ : 0 < p) (hp₁ : p < 1) :
    (fun n => liaHistory (paperDP T) n (liar T p n)) ≈ₙ fun _ => (p : ℝ) :=
  lic_paradox_resistance_ofDiagonal_unconditional T p hp₀ hp₁

end Asymptotic

end Cleanroom.Bli.BliExactness
