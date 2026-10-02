import Cleanroom.Bli.BliExtrapolation.Witnesses
import Cleanroom.Bli.BliExtrapolation.Extension

/-!
# `bli-extrapolation` · Product: product rules, the independence of coordinates, and when Soto's
rule is one (target 5d)

[[bli-soto-a-inventory]] 049 (PDF 01): the "independence" extrapolation — every new prime
independent of everything before it — and the conditional-chaining extrapolation coincide
exactly when the chaining rule does not look at the prefix. Three statements:

* **`productRule c`** (`p k w = c k`, independent of `w`), `CondRule.IsProduct`, and the cylinder
  factorisation `chainPMF_productRule : chainPMF (productRule c) k u = ∏_{j<k} bern c j (u j)`;
  at the measure level, `chainMeasure_productRule_indep`: the coordinate events
  `{v | v (e j) = u j}`, `j < k`, have the measure of their intersection equal to the product of
  their measures, for every `k` and `u` — "coordinates independent via cylinder factorisation", the
  form the mandate asks for (Mathlib has no `Measure.pi` on `ℕ → Bool`).
* **`sotoRule_eq_productRule_iff`**: for a structure whose axioms are semantically empty
  (`UnivStructure.TrivialAx`: every world is an `Ax`-world — PDF 01's `Ax = ∅`, under which the
  three clauses always give `½`, `axClause_eq_half_of_trivialAx`), Soto's rule is a product rule
  **on the positive-mass prefixes** (`SotoIsProductAe`) iff the base is a Bernoulli product
  (`IsProductBase`). The positive-mass qualification is not cosmetic: see the next item.
* **`sotoRule_guard_not_isProduct`**: the mandate's literal statement — "`sotoRule` is a product
  rule iff the base coordinates are independent" — is **false** as stated, because of the guarded
  division in `sotoRule` (`0` where the base marginal is null). `guardBase` is the product base
  with `q(T,·) = 0`, `q(F,T) = q(F,F) = ½` (parameters `c = (0, ½)`); `sotoRule` reads `0` on the
  null prefix `[T]` and `½` on `[F]`, so it is not a product rule although the base is a product.
  Recorded as finding F-13 (a mandate-level slip found by audit r2 fidelity B1 and verified here).

The null prefixes are exactly where the guard's junk value lives (`sotoRule`'s docstring), and
`sotoPMF_eq_baseMarginal` shows the pmf never sees it; a statement about the *rule*, as 5d is,
must quantify them away — or assume full support (`sotoRule_isProduct_iff_of_pos`).

Sources: [[bli-soto-a-inventory]] 049; PDF 01 (the two proposals); PDF 07 p. 2 ("Step 2").
-/

namespace Cleanroom.Bli.BliExtrapolation

open LogicalInduction LO.Propositional BoolPCWorld MeasureTheory Finset

/-! ## Product rules and the cylinder factorisation -/

/-- The Bernoulli factor of coordinate `j` for the value `b`: `c j` for `true`, `1 − c j` for
`false`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def bern (c : ℕ → ℚ) (j : ℕ) (b : Bool) : ℚ := if b then c j else 1 - c j

/-- `bern c j true = c j`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma bern_true (c : ℕ → ℚ) (j : ℕ) : bern c j true = c j := rfl

/-- `bern c j false = 1 − c j`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma bern_false (c : ℕ → ℚ) (j : ℕ) : bern c j false = 1 - c j := rfl

/-- The Bernoulli factors are in `[0,1]` when the parameters are.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma bern_mem_Icc {c : ℕ → ℚ} (hc : ∀ j, 0 ≤ c j ∧ c j ≤ 1) (j : ℕ) (b : Bool) :
    0 ≤ bern c j b ∧ bern c j b ≤ 1 := by
  cases b
  · simp only [bern_false]; constructor <;> linarith [hc j]
  · simpa using hc j

/-- **Product rule** (PDF 01's independence proposal as a chaining rule): the conditional of the
`(k+1)`-st enumerated atom is `c k`, whatever the prefix.
Source: [[bli-soto-a-inventory]] 049; PDF 01
Kind: D
Fidelity: exact -/
def productRule (c : ℕ → ℚ) : CondRule := fun k _ => c k

/-- A rule is a **product rule** iff its conditionals do not depend on the prefix.
Source: [[bli-soto-a-inventory]] 049 ("`p k w` independent of `w`")
Kind: D
Fidelity: exact -/
def CondRule.IsProduct (p : CondRule) : Prop := ∀ k (u w : FiniteWorld k), p k u = p k w

/-- `IsProduct` is "is some `productRule c`".
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma isProduct_iff (p : CondRule) : p.IsProduct ↔ ∃ c : ℕ → ℚ, p = productRule c := by
  constructor
  · intro h
    refine ⟨fun k => p k (fun _ => false), ?_⟩
    funext k u
    exact h k u _
  · rintro ⟨c, rfl⟩ k u w
    rfl

/-- `productRule c` takes values in `[0,1]` iff the parameters do.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma productRule_inUnit_iff (c : ℕ → ℚ) :
    (productRule c).InUnit ↔ ∀ j, 0 ≤ c j ∧ c j ≤ 1 :=
  ⟨fun h j => h j (fun _ => false), fun h k _ => h k⟩

/-- **Cylinder factorisation**: the chained pmf of a product rule is the product of the Bernoulli
factors of the coordinates.
Source: [[bli-soto-a-inventory]] 049; PDF 01
Kind: P
Fidelity: exact -/
theorem chainPMF_productRule (c : ℕ → ℚ) :
    ∀ (k : ℕ) (u : FiniteWorld k), chainPMF (productRule c) k u = ∏ j : Fin k, bern c j (u j)
  | 0, _ => by simp [chainPMF]
  | k + 1, u => by
      obtain ⟨u', b, rfl⟩ : ∃ (u' : FiniteWorld k) (b : Bool), u = Fin.snoc u' b :=
        ⟨Fin.init u, u (Fin.last k), (Fin.snoc_init_self u).symm⟩
      rw [chainPMF_snoc, chainPMF_productRule c k u', Fin.prod_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last, productRule]
      cases b <;> simp [bern]

/-- The coordinate event: the worlds reading `b` at the `j`-th enumerated atom.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def coordEvent (e : ℕ ≃ ℕ) (j : ℕ) (b : Bool) : Set BoolPCWorld := {v | v (e j) = b}

/-- The coordinate event is the event of the literal `lit (e j) b`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma coordEvent_eq (e : ℕ ≃ ℕ) (j : ℕ) (b : Bool) :
    coordEvent e j b = {v : BoolPCWorld | v.toPCWorld.Holds (lit (e j) b)} := by
  ext v
  simp only [coordEvent, Set.mem_setOf_eq, holds_lit, BoolPCWorld.toPCWorld]
  cases b <;> cases hv : v (e j) <;> simp

/-- A cylinder is the intersection of its coordinate events.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma cyl_eq_iInter_coordEvent (e : ℕ ≃ ℕ) {k : ℕ} (u : FiniteWorld k) :
    cyl e u = ⋂ j : Fin k, coordEvent e j (u j) := by
  ext v
  rw [mem_cyl_iff, Set.mem_iInter]
  rfl

/-- Under a product rule the literal `lit (e j) b` has value `bern c j b`
(`chainVal_and_atom` with `E = ⊤`).
Source: [[bli-soto-a-inventory]] 049
Kind: P
Fidelity: exact -/
theorem chainVal_productRule_lit (e : ℕ ≃ ℕ) (c : ℕ → ℚ) (j : ℕ) (b : Bool) :
    chainVal e (productRule c) (lit (e j) b) = bern c j b := by
  cases b
  · have h := chainVal_and_neg_atom e (productRule c) (E := ⊤) (k := j) (by simp) (c j)
      (fun _ _ => Or.inr rfl)
    rw [chainVal_top, mul_one] at h
    show chainVal e (productRule c) (lit (e j) false) = 1 - c j
    refine (chainVal_congr e _ ?_).trans h
    intro v
    simp [lit, PCWorld.holds_and, PCWorld.holds_top]
  · have h := chainVal_and_atom e (productRule c) (E := ⊤) (k := j) (by simp) (c j)
      (fun _ _ => Or.inr rfl)
    rw [chainVal_top, mul_one] at h
    show chainVal e (productRule c) (lit (e j) true) = c j
    refine (chainVal_congr e _ ?_).trans h
    intro v
    simp [lit, PCWorld.holds_and, PCWorld.holds_top]

/-- The chaining measure of a product rule gives the coordinate event `{v | v (e j) = b}` the
mass `bern c j b`.
Source: [[bli-soto-a-inventory]] 049
Kind: L
Fidelity: exact -/
theorem chainMeasure_productRule_coord (e : ℕ ≃ ℕ) {c : ℕ → ℚ} (hc : (productRule c).InUnit)
    (j : ℕ) (b : Bool) :
    chainMeasure e (productRule c) hc (coordEvent e j b) = ENNReal.ofReal (bern c j b) := by
  rw [coordEvent_eq, chainMeasure_sentence, chainVal_productRule_lit]

/-- The chaining measure of a product rule gives the cylinder `conj e u` the product of its
coordinates' Bernoulli masses.
Source: [[bli-soto-a-inventory]] 049; PDF 01
Kind: P
Fidelity: exact -/
theorem chainMeasure_productRule_cyl (e : ℕ ≃ ℕ) {c : ℕ → ℚ} (hc : (productRule c).InUnit)
    {k : ℕ} (u : FiniteWorld k) :
    chainMeasure e (productRule c) hc (cyl e u) =
      ∏ j : Fin k, ENNReal.ofReal (bern c j (u j)) := by
  rw [chainMeasure_conj, chainPMF_productRule, Rat.cast_prod, ENNReal.ofReal_prod_of_nonneg]
  intro j _
  exact_mod_cast (bern_mem_Icc ((productRule_inUnit_iff c).mp hc) j (u j)).1

/-- **5d, `chainMeasure_productRule_indep`** ("`chainMeasure_productRule_eq_pi`" of the mandate,
in the cylinder form): under a product rule the coordinate events `{v | v (e j) = u j}`, `j < k`,
are independent — the measure of their intersection is the product of their measures — for every
level `k` and every `u`. Since the cylinders determine the measure (`chainMeasure_unique`), this
is the product (Bernoulli) measure with parameters `c` along the enumeration; Mathlib's
`Measure.pi` is finite-index only, so the statement is the cylinder factorisation itself.
Source: [[bli-soto-a-inventory]] 049; PDF 01 ("independence")
Kind: P
Fidelity: variant: cylinder factorisation in place of `Measure.pi` (the mandate's own wording)
Hyps: (a) `(productRule c).InUnit` -/
theorem chainMeasure_productRule_indep (e : ℕ ≃ ℕ) {c : ℕ → ℚ} (hc : (productRule c).InUnit)
    {k : ℕ} (u : FiniteWorld k) :
    chainMeasure e (productRule c) hc (⋂ j : Fin k, coordEvent e j (u j)) =
      ∏ j : Fin k, chainMeasure e (productRule c) hc (coordEvent e j (u j)) := by
  rw [← cyl_eq_iInter_coordEvent, chainMeasure_productRule_cyl]
  simp only [chainMeasure_productRule_coord]

/-! ## Soto's rule as a product rule -/

/-- **Semantically empty axioms** (PDF 01's `Ax = ∅`): every world is an `Ax`-world. The three
clauses of Soto's rule then always give `½` (`axClause_eq_half_of_trivialAx`).
Source: [[bli-soto-a-inventory]] 049 ("with `Ax = ∅`")
Kind: D
Fidelity: exact (semantic form: `Ax S` consists of tautologies) -/
def UnivStructure.TrivialAx (S : UnivStructure) : Prop := ∀ v : PCWorld, AxHolds S v

/-- **Bernoulli product base**: `q w = ∏_{j<B} bern c j (w j)` for some parameters `c` — the
base's coordinates are independent under `q`.
Source: [[bli-soto-a-inventory]] 049 ("the base coordinates are independent under `q`")
Kind: D
Fidelity: exact -/
def IsProductBase {B : ℕ} (q : FiniteWorld B → ℚ) : Prop :=
  ∃ c : ℕ → ℚ, ∀ w : FiniteWorld B, q w = ∏ j : Fin B, bern c j (w j)

section Soto

variable (S : UnivStructure) [∀ Γ φ, Decidable (AxEntails S Γ φ)] (e : ℕ ≃ ℕ) {B : ℕ}

omit [∀ Γ φ, Decidable (AxEntails S Γ φ)] in
/-- Under semantically empty axioms no level-`k` conjunction entails either literal on the fresh
atom `e k` (flip it in the enumerated world).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma not_axEntails_lit_of_trivialAx (hS : S.TrivialAx) (k : ℕ) (u : FiniteWorld k) (b : Bool) :
    ¬ AxEntails S {conj e u} (lit (e k) b) := by
  intro h
  have hw := h (enumWorld e (Fin.snoc u (!b))).toPCWorld (hS _) ?_
  · rw [holds_lit] at hw
    simp only [BoolPCWorld.toPCWorld, enumWorld_snoc_last] at hw
    cases b <;> simp at hw
  · intro φ hφ
    rw [Finset.mem_singleton] at hφ
    subst hφ
    rw [holds_enumWorld_snoc_iff e u _ (level_conj_le e u)]
    exact (enumWorld_holds_conj_iff e u u).mpr rfl

/-- Under semantically empty axioms the three clauses always give `½`: PDF 01's independence
proposal beyond the base.
Source: [[bli-soto-a-inventory]] 049; PDF 07 p. 2 (the agnostic clause)
Kind: L
Fidelity: exact -/
lemma axClause_eq_half_of_trivialAx (hS : S.TrivialAx) (k : ℕ) (u : FiniteWorld k) :
    axClause S e k u = 1 / 2 := by
  have h1 := not_axEntails_lit_of_trivialAx S e hS k u true
  have h0 := not_axEntails_lit_of_trivialAx S e hS k u false
  simp only [lit, if_true, Bool.false_eq_true, if_false] at h1 h0
  simp [axClause, h1, h0]

/-- **Soto's rule is a product rule on the positive-mass prefixes**: some `c` with
`sotoRule S e q k u = c k` whenever the chained mass of `u` is not zero. The null prefixes are
excluded because that is where `sotoRule`'s guard reads its junk value `0`
(`sotoRule_guard_not_isProduct`).
Source: [[bli-soto-a-inventory]] 049 (with the guard qualification of audit r2 fidelity B1)
Kind: D
Fidelity: weaker: on positive-mass prefixes only (the literal "for all prefixes" is false,
`sotoRule_guard_not_isProduct`) -/
def SotoIsProductAe (q : FiniteWorld B → ℚ) : Prop :=
  ∃ c : ℕ → ℚ, ∀ (k : ℕ) (u : FiniteWorld k), sotoPMF S e q k u ≠ 0 → sotoRule S e q k u = c k

omit [∀ Γ φ, Decidable (AxEntails S Γ φ)] in
/-- The marginals of a Bernoulli product base are the Bernoulli products of the prefix (through
`baseMarginal_chainPMF`, since such a base is `chainPMF (productRule c) B`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma baseMarginal_of_product {q : FiniteWorld B → ℚ} {c : ℕ → ℚ}
    (hq : ∀ w : FiniteWorld B, q w = ∏ j : Fin B, bern c j (w j)) :
    ∀ (k : ℕ), k ≤ B → ∀ u : FiniteWorld k, baseMarginal q k u = ∏ j : Fin k, bern c j (u j) := by
  have hq' : q = chainPMF (productRule c) B := by
    funext w; rw [hq w, chainPMF_productRule]
  intro k hk u
  rw [hq', baseMarginal_chainPMF (productRule c) B k hk u, chainPMF_productRule]

/-- **5d, `sotoRule_eq_productRule_iff`**: for a structure with semantically empty axioms
(`Ax = ∅`) and a base `q` with `0 ≤ q`, `∑ q = 1`, Soto's rule is a product rule on the
positive-mass prefixes iff the base is a Bernoulli product. (⇐): below `B` the guarded conditional
of a product base is the parameter `c k` wherever the prefix has mass; from `B` on the three
clauses give `½`. (⇒): by induction on `k ≤ B` the marginals are `∏_{j<k} bern c j (u j)` — on a
null prefix both sides vanish, on a positive one the rule's value `c k` is the conditional — and
`q` is its own level-`B` marginal. The qualification "positive-mass" is forced by the guard:
`sotoRule_guard_not_isProduct`.
Source: [[bli-soto-a-inventory]] 049; PDF 01
Kind: P
Fidelity: weaker: on positive-mass prefixes (the mandate's literal form is false, F-13); `Ax = ∅`
rendered semantically as `TrivialAx`
Hyps: (a) `S.TrivialAx`; (a) `0 ≤ q`, `∑ q = 1` -/
theorem sotoRule_eq_productRule_iff (hS : S.TrivialAx) {q : FiniteWorld B → ℚ}
    (hq0 : ∀ w, 0 ≤ q w) (hq1 : ∑ w, q w = 1) :
    SotoIsProductAe S e q ↔ IsProductBase q := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    suffices h : ∀ (k : ℕ), k ≤ B → ∀ u : FiniteWorld k,
        baseMarginal q k u = ∏ j : Fin k, bern c j (u j) by
      intro w
      rw [← baseMarginal_self q w]
      exact h B le_rfl w
    intro k
    induction k with
    | zero =>
        intro _ u
        rw [baseMarginal_zero, hq1]
        simp
    | succ k ih =>
        intro hk u
        obtain ⟨u', b, rfl⟩ : ∃ (u' : FiniteWorld k) (b : Bool), u = Fin.snoc u' b :=
          ⟨Fin.init u, u (Fin.last k), (Fin.snoc_init_self u).symm⟩
        have hkB : k < B := hk
        have ihk := ih (Nat.le_of_succ_le hk) u'
        rw [Fin.prod_univ_castSucc]
        simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
        rw [← ihk]
        by_cases hM : baseMarginal q k u' = 0
        · rw [hM, zero_mul]
          apply le_antisymm _ (baseMarginal_nonneg hq0 _ _)
          rw [← hM]
          exact baseMarginal_snoc_le hq0 hk u' b
        · have hne : sotoPMF S e q k u' ≠ 0 := by
            rwa [sotoPMF_eq_baseMarginal S e hq0 hq1 k (Nat.le_of_succ_le hk) u']
          have hrule := hc k u' hne
          simp only [sotoRule, hkB, if_true, hM, if_false] at hrule
          have htrue : baseMarginal q (k + 1) (Fin.snoc u' true) = baseMarginal q k u' * c k := by
            rw [← hrule, mul_div_assoc', mul_div_cancel_left₀ _ hM]
          cases b
          · rw [bern_false]
            have hadd := baseMarginal_snoc_add q hk u'
            have hfalse : baseMarginal q (k + 1) (Fin.snoc u' false) =
                baseMarginal q k u' - baseMarginal q (k + 1) (Fin.snoc u' true) := by
              linarith
            rw [hfalse, htrue]
            ring
          · rw [bern_true]
            exact htrue
  · rintro ⟨c, hc⟩
    refine ⟨fun k => if k < B then c k else 1 / 2, ?_⟩
    intro k u hne
    by_cases hkB : k < B
    · simp only [sotoRule, hkB, if_true]
      have hM : baseMarginal q k u ≠ 0 := by
        rwa [sotoPMF_eq_baseMarginal S e hq0 hq1 k hkB.le u] at hne
      have hprod : (∏ j : Fin k, bern c j (u j)) ≠ 0 := by
        rwa [baseMarginal_of_product hc k hkB.le u] at hM
      rw [if_neg hM, baseMarginal_of_product hc k hkB.le u,
        baseMarginal_of_product hc (k + 1) hkB (Fin.snoc u true), Fin.prod_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last, bern_true]
      rw [mul_div_cancel_left₀ _ hprod]
    · simp only [sotoRule, hkB, if_false]
      exact axClause_eq_half_of_trivialAx S e hS k u

/-! ### The full-support form -/

omit [∀ Γ φ, Decidable (AxEntails S Γ φ)] in
/-- A strictly positive base has strictly positive marginals (the prefix extends to a base world).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma baseMarginal_pos_of_pos {q : FiniteWorld B → ℚ} (hq : ∀ w, 0 < q w) {k : ℕ} (hk : k ≤ B)
    (u : FiniteWorld k) : 0 < baseMarginal q k u := by
  unfold baseMarginal
  rw [dif_pos hk]
  set w₀ : FiniteWorld B := fun j => if h : (j : ℕ) < k then u ⟨j, h⟩ else false with hw₀
  have hext : Extends hk w₀ u := by
    intro j
    simp [hw₀, Fin.castLE, j.isLt]
  calc (0 : ℚ) < q w₀ := hq w₀
    _ = (if Extends hk w₀ u then q w₀ else 0) := by rw [if_pos hext]
    _ ≤ ∑ w, if Extends hk w u then q w else 0 :=
        Finset.single_le_sum (f := fun w => if Extends hk w u then q w else 0)
          (fun w _ => by split_ifs; exact (hq w).le; exact le_rfl) (Finset.mem_univ w₀)

/-- Under semantically empty axioms and a strictly positive base, every level-`k` conjunction has
strictly positive chained mass: below `B` by the marginals, beyond `B` by
`sotoPMF_pos_of_prefix_pos` (every conjunction is `Ax`-consistent when `Ax` is trivial).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sotoPMF_pos_of_trivialAx_of_pos (hS : S.TrivialAx) {q : FiniteWorld B → ℚ}
    (hq : ∀ w, 0 < q w) (hq1 : ∑ w, q w = 1) :
    ∀ (k : ℕ) (u : FiniteWorld k), 0 < sotoPMF S e q k u := by
  have hq0 : ∀ w, 0 ≤ q w := fun w => (hq w).le
  intro k u
  rcases le_or_gt k B with hk | hk
  · rw [sotoPMF_eq_baseMarginal S e hq0 hq1 k hk u]
    exact baseMarginal_pos_of_pos hq hk u
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk.le
    apply sotoPMF_pos_of_prefix_pos S e q d u
    · refine ⟨(enumWorld e u).toPCWorld, hS _, ?_⟩
      intro φ hφ
      rw [Finset.mem_singleton] at hφ
      subst hφ
      exact (enumWorld_holds_conj_iff e u u).mpr rfl
    · rw [sotoPMF_eq_baseMarginal S e hq0 hq1 B le_rfl]
      exact baseMarginal_pos_of_pos hq le_rfl _

/-- **5d, full-support form**: for a structure with semantically empty axioms and a *strictly
positive* base of mass one, Soto's rule is literally a product rule (`CondRule.IsProduct`, every
prefix) iff the base is a Bernoulli product — the guard never fires, so the positive-mass
qualification of `sotoRule_eq_productRule_iff` is discharged.
Source: [[bli-soto-a-inventory]] 049; PDF 01
Kind: C
Fidelity: exact under full support (`0 < q`); `Ax = ∅` rendered semantically
Hyps: (a) `S.TrivialAx`; (a) `0 < q`, `∑ q = 1` -/
theorem sotoRule_isProduct_iff_of_pos (hS : S.TrivialAx) {q : FiniteWorld B → ℚ}
    (hq : ∀ w, 0 < q w) (hq1 : ∑ w, q w = 1) :
    (sotoRule S e q).IsProduct ↔ IsProductBase q := by
  rw [isProduct_iff, ← sotoRule_eq_productRule_iff S e hS (fun w => (hq w).le) hq1]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, fun k u _ => by rw [hc]; rfl⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, funext fun k => funext fun u =>
      hc k u (sotoPMF_pos_of_trivialAx_of_pos S e hS hq hq1 k u).ne'⟩

/-! ## The guard counterexample: the literal statement is false -/

/-- The parameters `(0, ½, ½, …)`: the first coordinate is `false` with probability one.
Source: audit r2 fidelity B1 (the guard counterexample)
Kind: D
Fidelity: n/a -/
def guardC : ℕ → ℚ := fun k => if k = 0 then 0 else 1 / 2

/-- **The guard base**: the Bernoulli product with parameters `guardC` on two coordinates —
`q(T,·) = 0`, `q(F,T) = q(F,F) = ½`. A product base, nonnegative, of total mass one.
Source: audit r2 fidelity B1
Kind: D
Fidelity: n/a -/
def guardBase : FiniteWorld 2 → ℚ := chainPMF (productRule guardC) 2

/-- `guardBase` is a legitimate product base: nonnegative, total mass one, a Bernoulli product.
Source: audit r2 fidelity B1
Kind: L
Fidelity: n/a -/
theorem guardBase_props :
    (∀ w, 0 ≤ guardBase w) ∧ ∑ w, guardBase w = 1 ∧ IsProductBase guardBase := by
  have hc : (productRule guardC).InUnit := by
    rw [productRule_inUnit_iff]
    intro j
    unfold guardC
    split_ifs <;> norm_num
  exact ⟨fun w => chainPMF_nonneg hc 2 w, chainPMF_sum_one _ 2,
    ⟨guardC, fun w => chainPMF_productRule guardC 2 w⟩⟩

/-- On the guard base, `sotoRule` reads `0` on the null prefix `[T]` (the guard) and `½` on the
positive prefix `[F]` (the base's conditional `q(F,T)/q(F,·) = ½`).
Source: audit r2 fidelity B1
Kind: P
Fidelity: n/a -/
theorem sotoRule_guard_values :
    sotoRule S e guardBase 1 (fun _ => true) = 0 ∧
    sotoRule S e guardBase 1 (fun _ => false) = 1 / 2 := by
  have hM1 : baseMarginal guardBase 1 (fun _ => true) = 0 := by
    rw [guardBase, baseMarginal_chainPMF _ 2 1 (by norm_num)]
    simp [chainPMF, productRule, guardC]
  have hM0 : baseMarginal guardBase 1 (fun _ => false) = 1 := by
    rw [guardBase, baseMarginal_chainPMF _ 2 1 (by norm_num)]
    simp [chainPMF, productRule, guardC]
  have hM01 : baseMarginal guardBase 2 (Fin.snoc (fun _ => false) true) = 1 / 2 := by
    rw [guardBase, baseMarginal_self, chainPMF_snoc]
    simp [chainPMF, productRule, guardC]
  constructor
  · simp [sotoRule, hM1]
  · simp [sotoRule, hM0, hM01]

/-- **The literal 5d is false** (F-13): `guardBase` is a Bernoulli product
(`guardBase_props`), yet `sotoRule S e guardBase` is not a product rule — its level-`1` conditional
is `0` on the prefix `[T]` and `½` on `[F]` (`sotoRule_guard_values`). The guard's junk value on
null prefixes, invisible to the pmf (`sotoPMF_eq_baseMarginal`), is visible to a statement about
the rule; hence the positive-mass form of `sotoRule_eq_productRule_iff`.
Source: audit r2 fidelity B1; [[bli-soto-a-inventory]] 049
Kind: N+
Fidelity: n/a (a refutation of the mandate's literal wording, for every `S`, `e`)
Hyps: (a) none -/
theorem sotoRule_guard_not_isProduct : ¬ (sotoRule S e guardBase).IsProduct := by
  intro h
  have := h 1 (fun _ => true) (fun _ => false)
  rw [(sotoRule_guard_values S e).1, (sotoRule_guard_values S e).2] at this
  norm_num at this

end Soto

end Cleanroom.Bli.BliExtrapolation
