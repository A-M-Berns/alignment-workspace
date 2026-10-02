import Cleanroom.Bli.BliExtrapolation.Measure

/-!
# `bli-extrapolation` · Soto: the rule of record and its properties (target 3; design
decisions 5–6)

PDF 07 "Step 2" / PIBBSS §4.3: below the support copy the base `Q`; beyond it set
`P(C ∧ φ) := P(C)` if `Ax ∪ {C} ⊢_Prop φ`, `:= 0` if `⊢ ¬φ`, `:= ½ P(C)` otherwise. Here the base is
a world distribution `q : FiniteWorld B → ℚ` on the first `B` enumerated atoms (a coherent table
reaches it through `bli-finite`'s `IsWorldMarginal`), and `sotoRule S e q : CondRule` is (i) below
`B` the base's conditional where the base is positive and `0` where it is null (it does not matter
there: `sotoPMF_eq_baseMarginal` shows the chained pmf equals the base's marginals regardless),
(ii) from `B` on the three-clause `axClause`. The extrapolation is the chaining measure of that
rule (`extrapolate`), its rational valuation `extrapolateVal`. `BaseAxConsistent` names the
hypothesis "the base charges only `Ax`-consistent conjunctions" (design decision 6).

Claim (i) of the sources — "well-defined and `Ax`-consistent" — is `extrapolate_extends` +
`extrapolate_gaifman` (coherence, FAF's object) + `extrapolate_ae_Ax` (`Ax`-consistency as a.e.
satisfaction of every axiom); 3b is `extrapolateVal_eq_sum_axEntails`. Decidability of the rule
is relative to a `Local` instance (`axEntails_decidable`, `Syntax.lean`): the rule takes a
`Decidable` instance for `AxEntails S` explicitly; `extrapolate` is noncomputable anyway.

Sources: [[bli-soto-a-inventory]] 055, 053; [[bli-soto-a-2-inventory]] 008 ("Verification");
[[bli-soto-b-inventory]] 033; PDF 07 p. 2; PIBBSS §4.3 pp. 17–18.
-/

namespace Cleanroom.Bli.BliExtrapolation

open LogicalInduction LO.Propositional BoolPCWorld MeasureTheory Finset

/-! ## The base's marginals -/

section Base

variable {B : ℕ}

/-- `w : FiniteWorld B` extends `u : FiniteWorld k` (`k ≤ B`): agreement on the first `k`
coordinates.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def Extends {k : ℕ} (hk : k ≤ B) (w : FiniteWorld B) (u : FiniteWorld k) : Prop :=
  ∀ j : Fin k, w (Fin.castLE hk j) = u j

/-- `Extends` is decidable.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
instance {k : ℕ} (hk : k ≤ B) (w : FiniteWorld B) (u : FiniteWorld k) : Decidable (Extends hk w u) :=
  inferInstanceAs (Decidable (∀ j : Fin k, w (Fin.castLE hk j) = u j))

/-- **The base's marginal** on the first `k ≤ B` coordinates: the mass of the base worlds
extending `u` (`0` for `k > B`, never used there).
Source: PDF 07 p. 2 (`P((¬)φ₁ ∧ … ∧ (¬)φ_n) := Q(…)`); design decision 5
Kind: D
Fidelity: exact -/
def baseMarginal (q : FiniteWorld B → ℚ) (k : ℕ) (u : FiniteWorld k) : ℚ :=
  if hk : k ≤ B then ∑ w : FiniteWorld B, if Extends hk w u then q w else 0 else 0

/-- The marginal at level `B` is the base itself.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma baseMarginal_self (q : FiniteWorld B → ℚ) (u : FiniteWorld B) : baseMarginal q B u = q u := by
  unfold baseMarginal
  rw [dif_pos le_rfl]
  have : ∀ w : FiniteWorld B, Extends le_rfl w u ↔ w = u := by
    intro w
    constructor
    · intro h; funext j; simpa [Fin.castLE] using h j
    · rintro rfl j; rfl
  simp only [this]
  rw [Finset.sum_ite_eq' Finset.univ u]
  simp

/-- The marginal at level `0` is the total mass.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma baseMarginal_zero (q : FiniteWorld B → ℚ) (u : FiniteWorld 0) :
    baseMarginal q 0 u = ∑ w, q w := by
  unfold baseMarginal
  rw [dif_pos (Nat.zero_le B)]
  apply Finset.sum_congr rfl
  intro w _
  rw [if_pos]
  intro j; exact j.elim0

/-- Extending a `snoc`: agreement on the prefix and on the new coordinate.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma extends_snoc_iff {k : ℕ} (hk : k + 1 ≤ B) (w : FiniteWorld B) (u : FiniteWorld k)
    (b : Bool) :
    Extends hk w (Fin.snoc u b) ↔ Extends (Nat.le_of_succ_le hk) w u ∧ w ⟨k, hk⟩ = b := by
  unfold Extends
  rw [Fin.forall_fin_succ']
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun j => ?_, ?_⟩
    · have := h1 j
      rwa [show Fin.castLE hk (Fin.castSucc j) = Fin.castLE (Nat.le_of_succ_le hk) j from
        Fin.ext rfl] at this
    · rwa [show Fin.castLE hk (Fin.last k) = ⟨k, hk⟩ from Fin.ext rfl] at h2
  · rintro ⟨h1, h2⟩
    refine ⟨fun j => ?_, ?_⟩
    · rw [show Fin.castLE hk (Fin.castSucc j) = Fin.castLE (Nat.le_of_succ_le hk) j from
        Fin.ext rfl]
      exact h1 j
    · rwa [show Fin.castLE hk (Fin.last k) = ⟨k, hk⟩ from Fin.ext rfl]

/-- The two extensions of `u` carry the mass of `u` (the base's marginals are projective).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma baseMarginal_snoc_add (q : FiniteWorld B → ℚ) {k : ℕ} (hk : k + 1 ≤ B) (u : FiniteWorld k) :
    baseMarginal q (k + 1) (Fin.snoc u true) + baseMarginal q (k + 1) (Fin.snoc u false) =
      baseMarginal q k u := by
  simp only [baseMarginal, dif_pos hk, dif_pos (Nat.le_of_succ_le hk)]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w _
  simp only [extends_snoc_iff hk]
  by_cases h : Extends (Nat.le_of_succ_le hk) w u <;> cases hw : w ⟨k, hk⟩ <;> simp [h]

/-- Marginals of a nonnegative base are nonnegative.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma baseMarginal_nonneg {q : FiniteWorld B → ℚ} (hq : ∀ w, 0 ≤ q w) (k : ℕ) (u : FiniteWorld k) :
    0 ≤ baseMarginal q k u := by
  unfold baseMarginal
  split_ifs
  · exact Finset.sum_nonneg fun w _ => by split_ifs <;> simp [hq w]
  · exact le_rfl

/-- The mass of an extension is at most the mass of the prefix.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma baseMarginal_snoc_le {q : FiniteWorld B → ℚ} (hq : ∀ w, 0 ≤ q w) {k : ℕ} (hk : k + 1 ≤ B)
    (u : FiniteWorld k) (b : Bool) :
    baseMarginal q (k + 1) (Fin.snoc u b) ≤ baseMarginal q k u := by
  rw [← baseMarginal_snoc_add q hk u]
  cases b
  · exact le_add_of_nonneg_left (baseMarginal_nonneg hq _ _)
  · exact le_add_of_nonneg_right (baseMarginal_nonneg hq _ _)

/-- Extension transports truth of the prefix conjunction.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma holds_conj_of_extends (e : ℕ ≃ ℕ) {k : ℕ} (hk : k ≤ B) {w : FiniteWorld B} {u : FiniteWorld k}
    (hwu : Extends hk w u) {v : PCWorld} (hv : v.Holds (conj e w)) : v.Holds (conj e u) := by
  rw [conj_holds_iff] at hv ⊢
  intro j
  have := hv (Fin.castLE hk j)
  rw [hwu j] at this
  simpa [Fin.castLE] using this

/-! ## `Ax`-consistency is inherited -/

/-- The empty conjunction is `Ax`-consistent.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma axConsistent_conj_zero (S : UnivStructure) (e : ℕ ≃ ℕ) (u : FiniteWorld 0) : AxConsistent S {conj e u} := by
  obtain ⟨v, hv, _⟩ := Ax_satisfiable S
  refine ⟨v, hv, ?_⟩
  intro φ hφ
  rw [Finset.mem_singleton] at hφ
  subst hφ
  rw [conj_holds_iff]
  intro j; exact j.elim0

/-- `Ax`-consistency passes from an extension to its prefix.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma axConsistent_of_extends (S : UnivStructure) (e : ℕ ≃ ℕ) {k : ℕ} (hk : k ≤ B) {w : FiniteWorld B} {u : FiniteWorld k}
    (hwu : Extends hk w u) (h : AxConsistent S {conj e w}) : AxConsistent S {conj e u} := by
  obtain ⟨v, hv, hΓ⟩ := h
  refine ⟨v, hv, ?_⟩
  intro φ hφ
  rw [Finset.mem_singleton] at hφ
  subst hφ
  exact holds_conj_of_extends e hk hwu (hΓ _ (Finset.mem_singleton_self _))

/-- If `conj e (Fin.snoc u b)` is `Ax`-inconsistent but `conj e u` is not, then `conj e u`
`Ax`-entails the negation of the new literal.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma axEntails_neg_lit_of_inconsistent (S : UnivStructure) (e : ℕ ≃ ℕ) {k : ℕ} {u : FiniteWorld k} {b : Bool}
    (h : ¬ AxConsistent S {conj e (Fin.snoc u b)}) :
    AxEntails S {conj e u} (∼lit (e k) b) := by
  intro v hv hΓ
  rw [PCWorld.holds_neg]
  intro hlit
  apply h
  refine ⟨v, hv, ?_⟩
  intro φ hφ
  rw [Finset.mem_singleton] at hφ
  subst hφ
  rw [holds_conj_snoc_iff]
  exact ⟨hΓ _ (Finset.mem_singleton_self _), hlit⟩

end Base

/-! ## Soto's rule -/

section Rule

variable (S : UnivStructure) [∀ Γ φ, Decidable (AxEntails S Γ φ)] (e : ℕ ≃ ℕ) {B : ℕ}

/-- **The three clauses** of PDF 07 / PIBBSS §4.3 at a level beyond the support: `1` if
`Ax ∪ {C} ⊢_Prop φ`, `0` if `Ax ∪ {C} ⊢_Prop ¬φ`, `½` otherwise (`C = conj e u`, `φ = atom (e k)`).
Source: PDF 07 p. 2; PIBBSS §4.3 p. 18 ("Syntactic Coherence", "Agnostic clause");
[[bli-soto-a-2-inventory]] 008 ("Verification": confirmed clause by clause)
Kind: D
Fidelity: exact -/
def axClause (k : ℕ) (u : FiniteWorld k) : ℚ :=
  if AxEntails S {conj e u} (Formula.atom (e k)) then 1
  else if AxEntails S {conj e u} (∼Formula.atom (e k)) then 0 else 1 / 2

/-- **Soto's rule** (design decision 5): below `B` the base's conditional (a guarded division:
`0` where the base marginal is null — a junk value, proved irrelevant under `0 ≤ q`, `∑ q = 1`
by `sotoPMF_eq_baseMarginal`; for an unnormalized base the guard's value does matter and the
rule silently replaces the base, e.g. the zero base gives the point mass on the all-`false`
prefix), from `B` on the three clauses. The mandate's "never divides" is not literally met;
what is met is that no headline depends on the guard.
Source: PDF 07 p. 2 ("Step 2"); PIBBSS §4.3; [[bli-soto-a-inventory]] 055
Kind: D
Fidelity: exact (base regime: any conditional consistent with the base's marginals; `Ax`
regime: the three clauses verbatim) -/
def sotoRule (q : FiniteWorld B → ℚ) : CondRule := fun k u =>
  if k < B then
    (if baseMarginal q k u = 0 then 0
      else baseMarginal q (k + 1) (Fin.snoc u true) / baseMarginal q k u)
  else axClause S e k u

/-- The chained pmf of Soto's rule.
Source: PDF 07 p. 2
Kind: D
Fidelity: exact -/
abbrev sotoPMF (q : FiniteWorld B → ℚ) : (k : ℕ) → FiniteWorld k → ℚ := chainPMF (sotoRule S e q)

/-- Beyond the support the rule is the three-clause `axClause`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sotoRule_of_le (q : FiniteWorld B → ℚ) {k : ℕ} (hk : B ≤ k) (u : FiniteWorld k) :
    sotoRule S e q k u = axClause S e k u := by
  simp [sotoRule, not_lt.mpr hk]

/-- The three clauses take values in `{0, ½, 1}`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma axClause_mem (k : ℕ) (u : FiniteWorld k) :
    axClause S e k u = 0 ∨ axClause S e k u = 1 / 2 ∨ axClause S e k u = 1 := by
  unfold axClause
  split_ifs <;> simp

/-- Soto's rule takes values in `[0,1]` for a nonnegative base.
Source: PDF 06 p. 1 ("all our newly defined `p` are in `[0,1]`")
Kind: L
Fidelity: exact -/
lemma sotoRule_inUnit {q : FiniteWorld B → ℚ} (hq : ∀ w, 0 ≤ q w) : (sotoRule S e q).InUnit := by
  intro k u
  unfold sotoRule
  split_ifs with hkB hM
  · exact ⟨le_rfl, zero_le_one⟩
  · have hpos : 0 < baseMarginal q k u := lt_of_le_of_ne (baseMarginal_nonneg hq k u) (Ne.symm hM)
    constructor
    · exact div_nonneg (baseMarginal_nonneg hq _ _) hpos.le
    · rw [div_le_one hpos]
      exact baseMarginal_snoc_le hq hkB u true
  · rcases axClause_mem S e k u with h | h | h <;> rw [h] <;> norm_num

/-- **The chained pmf extends the base**: at every level `k ≤ B` it is the base's marginal
(for a nonnegative base of total mass one). This is the "`P((¬)φ₁ ∧ … ∧ (¬)φ_n) := Q(…)`"
clause and, at lower levels, PDF 06's "the large beliefs marginalize to the small".
Source: PDF 07 p. 2; PDF 06 p. 3 ("the large beliefs marginalize to the small … by definition")
Kind: P
Fidelity: exact
Hyps: (a) `0 ≤ q`, `∑ q = 1` -/
theorem sotoPMF_eq_baseMarginal {q : FiniteWorld B → ℚ} (hq0 : ∀ w, 0 ≤ q w)
    (hq1 : ∑ w, q w = 1) : ∀ (k : ℕ), k ≤ B → ∀ u : FiniteWorld k,
      sotoPMF S e q k u = baseMarginal q k u := by
  intro k
  induction k with
  | zero =>
      intro _ u
      rw [baseMarginal_zero, hq1]
      rfl
  | succ k ih =>
      intro hk u
      obtain ⟨u', b, rfl⟩ : ∃ (u' : FiniteWorld k) (b : Bool), u = Fin.snoc u' b :=
        ⟨Fin.init u, u (Fin.last k), (Fin.snoc_init_self u).symm⟩
      rw [sotoPMF, chainPMF_snoc, ← sotoPMF, ih (Nat.le_of_succ_le hk) u']
      have hkB : k < B := hk
      simp only [sotoRule, hkB, if_true]
      by_cases hM : baseMarginal q k u' = 0
      · rw [if_pos hM, hM, zero_mul]
        symm
        apply le_antisymm _ (baseMarginal_nonneg hq0 _ _)
        rw [← hM]
        exact baseMarginal_snoc_le hq0 hk u' b
      · rw [if_neg hM]
        cases b
        · simp only [Bool.false_eq_true, if_false]
          have hc : baseMarginal q k u' * (baseMarginal q (k + 1) (Fin.snoc u' true) /
              baseMarginal q k u') = baseMarginal q (k + 1) (Fin.snoc u' true) := by
            rw [mul_div_assoc', mul_div_cancel_left₀ _ hM]
          rw [mul_sub, mul_one, hc]
          linarith [baseMarginal_snoc_add q hk u']
        · simp only [if_true]
          rw [mul_div_assoc', mul_div_cancel_left₀ _ hM]

/-- The chained pmf at level `B` is the base.
Source: PDF 07 p. 2
Kind: L
Fidelity: exact -/
theorem sotoPMF_base {q : FiniteWorld B → ℚ} (hq0 : ∀ w, 0 ≤ q w) (hq1 : ∑ w, q w = 1)
    (u : FiniteWorld B) : sotoPMF S e q B u = q u := by
  rw [sotoPMF_eq_baseMarginal S e hq0 hq1 B le_rfl u, baseMarginal_self]

/-! ## The extrapolation -/

/-- **Soto's extrapolation** of the base `q` (design decision 5): the conditional-chaining
measure of `sotoRule S e q`, a probability measure on `BoolPCWorld` (FAF's `gaifmanMeasure` of
the chained valuation, decision 4 route α). The object of record for limit statements. It takes
only `0 ≤ q`: an unnormalized base is accepted and silently replaced by the chain of the guarded
conditionals (see `sotoRule`); every base-facing headline carries `∑ q = 1`, under which the
level-`B` chain is `q` itself (`sotoPMF_base`).
Source: PDF 07 p. 2 ("Step 2"); PIBBSS §4.3; [[bli-soto-a-inventory]] 055; [[bli-soto-b-inventory]] 033
(`Future` clause dropped, per the plan)
Kind: D
Fidelity: variant: quantifier structure abstracted (design decision 1); `Future` clause dropped -/
noncomputable def extrapolate (q : FiniteWorld B → ℚ) (hq : ∀ w, 0 ≤ q w) : Measure BoolPCWorld :=
  chainMeasure e (sotoRule S e q) (sotoRule_inUnit S e hq)

/-- `extrapolate` is a probability measure.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
instance extrapolate_isProbabilityMeasure (q : FiniteWorld B → ℚ) (hq : ∀ w, 0 ≤ q w) :
    IsProbabilityMeasure (extrapolate S e q hq) := by
  unfold extrapolate
  infer_instance

/-- **Soto's extrapolation, rational valuation**: the chained valuation of `sotoRule S e q` — the
value `P(φ) := Σ_{C ⊨ φ} P(C)`; Lean-computable (a `def`, not `noncomputable`) when `AxEntails S`
is decidable (a `Local` instance) — no `Primrec`/`Computable` statement is made or implied.
Source: PDF 07 p. 2 (`P(φ) := Σ_{C ⊢_Prop φ} P(C)`)
Kind: D
Fidelity: variant: quantifier structure abstracted (design decision 1) -/
def extrapolateVal (q : FiniteWorld B → ℚ) : Sentence → ℚ := chainVal e (sotoRule S e q)

/-- **`Ax`-consistent base** (design decision 6): every base world of nonzero mass is
`Ax`-consistent. The hypothesis PDF 07 p. 2 states as "by assumption `Q` was already consistent
with `Ax`".
Source: PDF 07 p. 2; PIBBSS §4.3
Kind: D
Fidelity: exact -/
def BaseAxConsistent (q : FiniteWorld B → ℚ) : Prop :=
  ∀ u : FiniteWorld B, q u ≠ 0 → AxConsistent S {conj e u}

/-- The extrapolation's event identity (from `chainMeasure_sentence`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem extrapolate_sentence {q : FiniteWorld B → ℚ} (hq : ∀ w, 0 ≤ q w) (φ : Sentence) :
    extrapolate S e q hq {v : BoolPCWorld | v.toPCWorld.Holds φ} =
      ENNReal.ofReal (extrapolateVal S e q φ) :=
  chainMeasure_sentence e _ φ

/-- **The extrapolation extends the base** (target 3a): every support cylinder `conj e u`,
`u : FiniteWorld B`, has measure `ofReal (q u)`. Stated over an abstract quantifier structure `S`
(decision 1) and an enumeration `e` (decision 3); the measure is FAF's `gaifmanMeasure` of the
chained valuation (decision 4, route α).
Source: PDF 07 p. 2 (`P((¬)φ₁ ∧ … ∧ (¬)φ_n) := Q(…)`); PDF 06 p. 3 ("large beliefs marginalize
to the small")
Kind: P
Fidelity: exact
Hyps: (a) `0 ≤ q`, `∑ q = 1` -/
theorem extrapolate_extends {q : FiniteWorld B → ℚ} (hq0 : ∀ w, 0 ≤ q w) (hq1 : ∑ w, q w = 1)
    (u : FiniteWorld B) : extrapolate S e q hq0 (cyl e u) = ENNReal.ofReal (q u) := by
  unfold extrapolate
  rw [chainMeasure_conj, ← sotoPMF, sotoPMF_base S e hq0 hq1]

/-- **Small sentences are priced by the base** (`extrapolateVal_eq_base`): on a sentence whose
atoms are among the first `B` enumerated atoms, the extrapolation is the base's world sum. This is
the strongest form of "the large beliefs marginalize to the small" (PDF 06) and what
`extrapolate_conditional_small` (3d) reads off.
Source: PDF 06 p. 3; PDF 07 p. 2
Kind: P
Fidelity: exact
Hyps: (a) `0 ≤ q`, `∑ q = 1` -/
theorem extrapolateVal_eq_base {q : FiniteWorld B → ℚ} (hq0 : ∀ w, 0 ≤ q w) (hq1 : ∑ w, q w = 1)
    {φ : Sentence} (hφ : level e φ ≤ B) :
    extrapolateVal S e q φ =
      ∑ u : FiniteWorld B, if (enumWorld e u).toPCWorld.Holds φ then q u else 0 := by
  unfold extrapolateVal
  rw [← chainValAt_eq_of_le e _ hφ]
  unfold chainValAt
  apply Finset.sum_congr rfl
  intro u _
  rw [← sotoPMF, sotoPMF_base S e hq0 hq1]

/-- **3d, `extrapolate_conditional_small`** ([[bli-soto-a-inventory]] 053): for `φ`, `ψ` with atoms
among the first `B` enumerated atoms, the extrapolation's conditional of `φ` given `ψ` is the
base's, in product form (`P(φ ∧ ψ) · Q(ψ) = Q(φ ∧ ψ) · P(ψ)`; no `conditionalQuote`, junk-free at
`Q(ψ) = 0`). This is why Soto's "sensible action consequences" desideratum is automatic *only*
when the conditioning sentence is small; for a large `A(Q̂) = a` nothing here applies (the content
of 011–012 in the parent inventory). A corollary of `extrapolateVal_eq_base`, which says more.
Source: PDF 06 p. 3 ("Decision theory"); [[bli-soto-a-inventory]] 053
Kind: T (after `extrapolateVal_eq_base` on both sides it is `a·b = a·b`; the content is
`extrapolateVal_eq_base`)
Fidelity: exact
Hyps: (a) `0 ≤ q`, `∑ q = 1` -/
theorem extrapolate_conditional_small {q : FiniteWorld B → ℚ} (hq0 : ∀ w, 0 ≤ q w)
    (hq1 : ∑ w, q w = 1) {φ ψ : Sentence} (hφ : level e φ ≤ B) (hψ : level e ψ ≤ B) :
    extrapolateVal S e q (φ ⋏ ψ) *
        (∑ u : FiniteWorld B, if (enumWorld e u).toPCWorld.Holds ψ then q u else 0) =
      (∑ u : FiniteWorld B, if (enumWorld e u).toPCWorld.Holds (φ ⋏ ψ) then q u else 0) *
        extrapolateVal S e q ψ := by
  rw [extrapolateVal_eq_base S e hq0 hq1 (by simp [hφ, hψ]), extrapolateVal_eq_base S e hq0 hq1 hψ]

omit [∀ Γ φ, Decidable (AxEntails S Γ φ)] in
/-- An `Ax`-inconsistent prefix of the support carries no base mass.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma baseMarginal_eq_zero_of_inconsistent {q : FiniteWorld B → ℚ} (hbase : BaseAxConsistent S e q)
    {k : ℕ} (hk : k ≤ B) {u : FiniteWorld k} (hu : ¬ AxConsistent S {conj e u}) :
    baseMarginal q k u = 0 := by
  unfold baseMarginal
  rw [dif_pos hk]
  apply Finset.sum_eq_zero
  intro w _
  split_ifs with hwu
  · by_contra hq
    exact hu (axConsistent_of_extends S e hk hwu (hbase w hq))
  · rfl

/-- **`Ax`-inconsistent conjunctions stay null** (target 3a): at every level, a conjunction that
is not `Ax`-consistent has chained mass zero. Below the support this is `BaseAxConsistent`; from
`B` on it is the mechanism of decision 5's clauses: if `conj u ∧ lit` is inconsistent and `conj u`
consistent then `Ax ∪ {conj u}` entails `∼lit`, so the factor is `0`.
Source: PDF 07 p. 2 ("immediate to prove by induction that … `P` is consistent with `Ax`")
Kind: P
Fidelity: exact
Hyps: (a) `0 ≤ q`, `∑ q = 1`, `BaseAxConsistent` -/
theorem sotoPMF_zero_of_inconsistent {q : FiniteWorld B → ℚ} (hq0 : ∀ w, 0 ≤ q w)
    (hq1 : ∑ w, q w = 1) (hbase : BaseAxConsistent S e q) :
    ∀ (k : ℕ) (u : FiniteWorld k), ¬ AxConsistent S {conj e u} → sotoPMF S e q k u = 0 := by
  intro k
  induction k with
  | zero => intro u hu; exact absurd (axConsistent_conj_zero S e u) hu
  | succ k ih =>
      intro u hu
      obtain ⟨u', b, rfl⟩ : ∃ (u' : FiniteWorld k) (b : Bool), u = Fin.snoc u' b :=
        ⟨Fin.init u, u (Fin.last k), (Fin.snoc_init_self u).symm⟩
      by_cases hkB : k + 1 ≤ B
      · rw [sotoPMF_eq_baseMarginal S e hq0 hq1 _ hkB]
        exact baseMarginal_eq_zero_of_inconsistent S e hbase hkB hu
      · rw [sotoPMF, chainPMF_snoc]
        by_cases hu' : AxConsistent S {conj e u'}
        · have hneg := axEntails_neg_lit_of_inconsistent S e hu
          rw [sotoRule_of_le S e q (by omega) u']
          cases b
          · have h1 : AxEntails S {conj e u'} (Formula.atom (e k)) := by
              intro v hv hΓ
              have := hneg v hv hΓ
              simpa [lit] using this
            simp [axClause, h1]
          · have h0 : AxEntails S {conj e u'} (∼Formula.atom (e k)) := by
              simpa [lit] using hneg
            have h1 : ¬ AxEntails S {conj e u'} (Formula.atom (e k)) :=
              fun h => not_axEntails_both hu' h h0
            simp [axClause, h1, h0]
        · rw [← sotoPMF, ih u' hu', zero_mul]

/-- The negation of every axiom has extrapolated value zero.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem extrapolateVal_neg_ax {q : FiniteWorld B → ℚ} (hq0 : ∀ w, 0 ≤ q w) (hq1 : ∑ w, q w = 1)
    (hbase : BaseAxConsistent S e q) {a : Sentence} (ha : a ∈ Ax S) :
    extrapolateVal S e q (∼a) = 0 := by
  unfold extrapolateVal
  apply chainVal_eq_zero_of_le e _ le_rfl
  intro u hu
  apply sotoPMF_zero_of_inconsistent S e hq0 hq1 hbase
  rintro ⟨v, hv, hΓ⟩
  have hconj : v.Holds (conj e u) := hΓ _ (Finset.mem_singleton_self _)
  have hlev : level e (∼a) ≤ level e (∼a) := le_rfl
  have := (holds_congr_of_holds_conj_pc e hlev hconj).mpr hu
  exact (PCWorld.holds_neg v a).mp this (hv a ha)

/-- **The extrapolation is `Ax`-a.e.** (target 3a, load-bearing; claim (i)'s "`P` is consistent with
`Ax`"): almost every world of `extrapolate S e q` satisfies every axiom of `Ax S` — from
`sotoPMF_zero_of_inconsistent` (2c + countability of `Ax S`). Stated over an abstract quantifier
structure `S` (decision 1) and an enumeration `e` (decision 3); the measure is FAF's
`gaifmanMeasure` of the chained valuation (decision 4, route α). "`Ax`-consistency" is rendered
as a.e. satisfaction, not as a syntactic consistency claim.
Source: PDF 07 p. 2 ("it's immediate to prove by induction that this is well-defined and that
`P` is consistent with `Ax`"); PIBBSS §4.3 p. 18; [[bli-soto-a-inventory]] 055;
[[bli-soto-b-inventory]] 033 (i)
Kind: P
Fidelity: exact (given decision 1)
Hyps: (a) `0 ≤ q`, `∑ q = 1`; (a) `BaseAxConsistent S e q` (discharged by every witness in
`Witnesses.lean`) -/
theorem extrapolate_ae_Ax {q : FiniteWorld B → ℚ} (hq0 : ∀ w, 0 ≤ q w) (hq1 : ∑ w, q w = 1)
    (hbase : BaseAxConsistent S e q) :
    ∀ᵐ v ∂extrapolate S e q hq0, AxHolds S v.toPCWorld :=
  chainMeasure_ae_all e _ (Ax S) (fun _ ha => extrapolateVal_neg_ax S e hq0 hq1 hbase ha)

/-- **The extrapolation is Gaifman-coherent** (target 3a; claim (i)'s "well-defined and
coherent", rendered as FAF's `GaifmanCoherent`): an instance of `chainVal_gaifman`.
Source: PDF 07 p. 2; PDF 06 p. 1; PIBBSS §4.3 (i)
Kind: L (one application of `chainVal_gaifman`)
Fidelity: exact
Hyps: (a) `0 ≤ q` -/
theorem extrapolate_gaifman {q : FiniteWorld B → ℚ} (hq0 : ∀ w, 0 ≤ q w) :
    GaifmanCoherent (fun φ => (extrapolateVal S e q φ : ℝ)) :=
  chainVal_gaifman e (sotoRule_inUnit S e hq0)

/-- **3b**: Soto writes `P(φ) = Σ_{C ⊢_Prop φ} P(C) = Σ_{Ax ∪ {C} ⊢_Prop φ} P(C)` without comment;
the two sums differ exactly on the `Ax`-inconsistent `C`, which `sotoPMF_zero_of_inconsistent`
makes null. Here: the extrapolated value is the sum over the level-`level e φ` conjunctions that
`Ax`-entail `φ`.
Source: PDF 07 p. 2; PIBBSS §4.3 p. 18
Kind: P
Fidelity: exact
Hyps: (a) `0 ≤ q`, `∑ q = 1`, `BaseAxConsistent` -/
theorem extrapolateVal_eq_sum_axEntails {q : FiniteWorld B → ℚ} (hq0 : ∀ w, 0 ≤ q w)
    (hq1 : ∑ w, q w = 1) (hbase : BaseAxConsistent S e q) (φ : Sentence) :
    extrapolateVal S e q φ =
      ∑ u : FiniteWorld (level e φ),
        if AxEntails S {conj e u} φ then sotoPMF S e q (level e φ) u else 0 := by
  unfold extrapolateVal chainVal chainValAt
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu : AxConsistent S {conj e u}
  · have hiff : AxEntails S {conj e u} φ ↔ (enumWorld e u).toPCWorld.Holds φ := by
      constructor
      · intro h
        obtain ⟨v, hv, hΓ⟩ := hu
        have hconj : v.Holds (conj e u) := hΓ _ (Finset.mem_singleton_self _)
        exact (holds_congr_of_holds_conj_pc e le_rfl hconj).mp (h v hv hΓ)
      · intro h v hv hΓ
        have hconj : v.Holds (conj e u) := hΓ _ (Finset.mem_singleton_self _)
        exact (holds_congr_of_holds_conj_pc e le_rfl hconj).mpr h
    simp only [hiff]
  · have h0 := sotoPMF_zero_of_inconsistent S e hq0 hq1 hbase _ u hu
    rw [← sotoPMF, h0]
    simp

end Rule

end Cleanroom.Bli.BliExtrapolation
