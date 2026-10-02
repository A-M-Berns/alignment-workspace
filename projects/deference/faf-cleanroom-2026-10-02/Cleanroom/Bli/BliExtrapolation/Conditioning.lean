import Cleanroom.Bli.BliExtrapolation.Soto

/-!
# `bli-extrapolation` · Conditioning: conditioning re-runs the chain; constraints are
definitional in the chaining framework (target 5)

* **5a** `chainMeasure_cond_cylinder`: conditioning the chaining measure on a level-`k` cylinder
  `conj e w` of positive mass is the chaining measure of the rule that is the point mass at `w`
  below level `k` and the original rule from `k` on (`condRule p w`). Mathlib's
  `ProbabilityTheory.cond` at a null event is the zero measure, so positivity is in the statement.
  Corollary `extrapolate_cond_cylinder` for Soto's extrapolation: conditioning on a written-out
  earlier state re-runs the same clauses from that state.
* **5b** `constraint2Rule`/`constraint2_definitional` and `introspectionRule`/
  `introspection_definitional`: BLI constraint 2 (`P(E_r ∧ φ) = r · P(E_r)` for the event atoms
  `E_r = ⌜P_{n+1}(φ) = r⌝`) and exact introspection (`P(⌜P(φ) < p⌝) = 1[P(φ) < p]`) are
  *definitional* for a large sentence: choose the rule at the sentence's level accordingly. These
  are two rules and one lemma each, with **no** bridge to `bli-found`'s `E2x`/`E2i` (those are
  predicates on a `History`; this is one measure). The introspection rule is legal only when the
  quoted sentence's level is below the quoting atom's (PDF 07's `⌜⌜φ⌝⌝ > ⌜φ⌝`).
* **5c** `chain_inside_support_fixed` (a small sentence's joint value is the base's) and
  `partition_gives_balance` (from a partition of unity and constraint 2 on each cell, constraint 4).

Sources: PIBBSS §4.3 p. 18 ("when conditioned on … the complete state description of a state,
it nicely extrapolates its finite beliefs into the infinite automatically"); PDF 06 p. 1;
PDF 07 pp. 4–5 ("Introspection"); [[bli-soto-a-2-inventory]] 005; [[bli-soto-b-inventory]] 033 (iv).
-/

namespace Cleanroom.Bli.BliExtrapolation

open LogicalInduction LO.Propositional BoolPCWorld MeasureTheory ProbabilityTheory Finset

/-! ## Prefixes -/

/-- The first `k` coordinates of a level-`j` world (`k ≤ j`).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def prefixOf {j k : ℕ} (hk : k ≤ j) (u : FiniteWorld j) : FiniteWorld k :=
  fun i => u (Fin.castLE hk i)

/-- The prefix of `Fin.snoc u b` is the prefix of `u` (for `k ≤ j`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma prefixOf_snoc {j k : ℕ} (hk : k ≤ j) (u : FiniteWorld j) (b : Bool) :
    prefixOf (hk.trans (Nat.le_succ j)) (Fin.snoc u b) = prefixOf hk u := by
  funext i
  simp only [prefixOf]
  rw [show Fin.castLE (hk.trans (Nat.le_succ j)) i = Fin.castSucc (Fin.castLE hk i) from
    Fin.ext rfl, Fin.snoc_castSucc]

/-- The full prefix is the world itself.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma prefixOf_self {j : ℕ} (u : FiniteWorld j) : prefixOf le_rfl u = u := by
  funext i; simp [prefixOf]

/-- `Fin.snoc (prefixOf u) (u k) = prefixOf u` at level `k+1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma prefixOf_succ {j k : ℕ} (hk : k + 1 ≤ j) (u : FiniteWorld j) :
    prefixOf hk u =
      (Fin.snoc (prefixOf (Nat.le_of_succ_le hk) u) (u ⟨k, hk⟩) : FiniteWorld (k + 1)) := by
  conv_lhs => rw [← Fin.snoc_init_self (prefixOf hk u)]
  rfl

/-- A world holds `conj e u` iff it agrees with `u` on the first `j` enumerated atoms, restated
through prefixes: it holds `conj e (prefixOf hk u)` too.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_cyl_of_mem_cyl_prefix (e : ℕ ≃ ℕ) {j k : ℕ} (hk : k ≤ j) (u : FiniteWorld j)
    {v : BoolPCWorld} (hv : v ∈ cyl e u) : v ∈ cyl e (prefixOf hk u) := by
  rw [mem_cyl_iff] at hv ⊢
  intro i
  simpa [prefixOf] using hv (Fin.castLE hk i)

/-- The cylinder of `u` meets the cylinder of a lower-level `w` exactly when `w` is `u`'s prefix.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma cyl_inter_cyl_of_le (e : ℕ ≃ ℕ) {j k : ℕ} (hk : k ≤ j) (w : FiniteWorld k)
    (u : FiniteWorld j) :
    cyl e w ∩ cyl e u = if prefixOf hk u = w then cyl e u else ∅ := by
  split_ifs with h
  · ext v
    constructor
    · exact fun hv => hv.2
    · intro hv
      exact ⟨h ▸ mem_cyl_of_mem_cyl_prefix e hk u hv, hv⟩
  · ext v
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro hw hu
    apply h
    funext i
    rw [mem_cyl_iff] at hw hu
    simp only [prefixOf]
    rw [← hu (Fin.castLE hk i), ← hw i]
    rfl

/-! ## 5a — conditioning on a cylinder -/

/-- **The conditioned rule**: the point mass at `w` below level `k` (coordinate `j < k` is forced to
`w j`), the original rule from `k` on.
Source: PIBBSS §4.3 p. 18 (conditioning on a complete state description); [[bli-soto-b-inventory]]
033 (iv)
Kind: D
Fidelity: exact -/
def condRule (p : CondRule) {k : ℕ} (w : FiniteWorld k) : CondRule := fun j u =>
  if h : j < k then (if w ⟨j, h⟩ then 1 else 0) else p j u

/-- The conditioned rule takes values in `[0,1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma condRule_inUnit {p : CondRule} (hp : p.InUnit) {k : ℕ} (w : FiniteWorld k) :
    (condRule p w).InUnit := by
  intro j u
  unfold condRule
  split_ifs
  · exact ⟨zero_le_one, le_rfl⟩
  · exact ⟨le_rfl, zero_le_one⟩
  · exact hp j u

/-- Below level `k`, the conditioned chain is the indicator of "`u` is a prefix of `w`".
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma chainPMF_condRule_of_le (p : CondRule) {k : ℕ} (w : FiniteWorld k) :
    ∀ (j : ℕ) (hj : j ≤ k) (u : FiniteWorld j),
      chainPMF (condRule p w) j u = if u = prefixOf hj w then 1 else 0 := by
  intro j
  induction j with
  | zero =>
      intro _ u
      rw [if_pos (Subsingleton.elim _ _)]
      rfl
  | succ j ih =>
      intro hj u
      obtain ⟨u', b, rfl⟩ : ∃ (u' : FiniteWorld j) (b : Bool), u = (Fin.snoc u' b : FiniteWorld (j + 1)) :=
        ⟨Fin.init u, u (Fin.last j), (Fin.snoc_init_self u).symm⟩
      rw [chainPMF_snoc, ih (Nat.le_of_succ_le hj) u', prefixOf_succ hj w]
      have hjk : j < k := hj
      simp only [condRule, hjk, dite_true]
      by_cases hu : u' = prefixOf (Nat.le_of_succ_le hj) w
      · subst hu
        cases b <;> cases hw : w ⟨j, hj⟩ <;> simp [Fin.snoc_inj]
      · have : (Fin.snoc u' b : FiniteWorld (j + 1)) ≠
            Fin.snoc (prefixOf (Nat.le_of_succ_le hj) w) (w ⟨j, hj⟩) := by
          intro h
          exact hu (Fin.snoc_inj.mp h).1
        simp [hu, this]

/-- From level `k` on, the original chain times the conditioned chain is the original chain on
the worlds extending `w` and `0` elsewhere: `chainPMF p k w · chainPMF (condRule p w) j u =
[prefix u = w] · chainPMF p j u`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma chainPMF_mul_condRule (p : CondRule) {k : ℕ} (w : FiniteWorld k) :
    ∀ (j : ℕ) (hj : k ≤ j) (u : FiniteWorld j),
      chainPMF p k w * chainPMF (condRule p w) j u =
        if prefixOf hj u = w then chainPMF p j u else 0 := by
  intro j
  induction j with
  | zero =>
      intro hj u
      obtain rfl : k = 0 := Nat.le_zero.mp hj
      rw [chainPMF_condRule_of_le p w 0 le_rfl u]
      rw [if_pos (Subsingleton.elim _ _), if_pos (Subsingleton.elim _ _)]
      simp [chainPMF]
  | succ j ih =>
      intro hj u
      obtain ⟨u', b, rfl⟩ : ∃ (u' : FiniteWorld j) (b : Bool), u = (Fin.snoc u' b : FiniteWorld (j + 1)) :=
        ⟨Fin.init u, u (Fin.last j), (Fin.snoc_init_self u).symm⟩
      rcases Nat.lt_or_ge j k with hlt | hge
      · -- j + 1 = k: the base case of the `Ax` regime
        obtain rfl : k = j + 1 := le_antisymm hj hlt
        rw [chainPMF_condRule_of_le p w (j + 1) le_rfl, prefixOf_self,
          show prefixOf hj (Fin.snoc u' b : FiniteWorld (j + 1)) = Fin.snoc u' b from prefixOf_self _]
        by_cases h : (Fin.snoc u' b : FiniteWorld (j + 1)) = w
        · subst h; simp
        · simp [h]
      · rw [chainPMF_snoc, chainPMF_snoc, ← mul_assoc, ih hge u', prefixOf_snoc hge u' b]
        have hnlt : ¬ j < k := not_lt.mpr hge
        simp only [condRule, hnlt, dite_false]
        split_ifs <;> simp

/-- **5a, `chainMeasure_cond_cylinder`** (P): conditioning the chaining measure on the level-`k`
cylinder of `w` (of positive mass) is the chaining measure of `condRule p w` — "conditioning on a
written-out earlier state re-runs the same extrapolation from that state". Mathlib's `cond` at a
null event is the zero measure, so the positivity hypothesis is in the statement. Proof: both
sides give every enumerated cylinder the same mass (`chainMeasure_unique`).
Source: PIBBSS §4.3 p. 18; [[bli-soto-b-inventory]] 033 (iv)
Kind: P
Fidelity: variant: `Future` clause dropped (plan); the conditioning event is a level-`k`
conjunction
Hyps: (a) `p.InUnit`; (a) `0 < chainPMF p k w` -/
theorem chainMeasure_cond_cylinder (e : ℕ ≃ ℕ) {p : CondRule} (hp : p.InUnit) {k : ℕ}
    (w : FiniteWorld k) (hw : 0 < chainPMF p k w) :
    (chainMeasure e p hp)[|cyl e w] = chainMeasure e (condRule p w) (condRule_inUnit hp w) := by
  have hm : (chainMeasure e p hp) (cyl e w) = ENNReal.ofReal (chainPMF p k w) :=
    chainMeasure_conj e hp w
  have hm0 : (chainMeasure e p hp) (cyl e w) ≠ 0 := by
    rw [hm, ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact_mod_cast hw
  have hmtop : (chainMeasure e p hp) (cyl e w) ≠ ⊤ := measure_ne_top _ _
  haveI : IsProbabilityMeasure ((chainMeasure e p hp)[|cyl e w]) :=
    cond_isProbabilityMeasure hm0
  apply chainMeasure_unique e (condRule_inUnit hp w)
  intro j u
  rw [cond_apply (measurableSet_cyl e w)]
  rcases le_or_gt j k with hj | hj
  · rw [Set.inter_comm, cyl_inter_cyl_of_le e hj u w, chainPMF_condRule_of_le p w j hj u]
    by_cases h : u = prefixOf hj w
    · rw [if_pos h.symm, if_pos h, ENNReal.inv_mul_cancel hm0 hmtop]; simp
    · rw [if_neg (Ne.symm h), if_neg h]; simp
  · rw [cyl_inter_cyl_of_le e hj.le w u]
    have hmul := chainPMF_mul_condRule p w j hj.le u
    split_ifs with h
    · rw [if_pos h] at hmul
      rw [chainMeasure_conj e hp u, chainMeasure_conj e hp w, ← hmul]
      have hwR : (0 : ℝ) < chainPMF p k w := by exact_mod_cast hw
      rw [show ((chainPMF p k w * chainPMF (condRule p w) j u : ℚ) : ℝ) =
          (chainPMF p k w : ℝ) * (chainPMF (condRule p w) j u : ℝ) by push_cast; ring,
        ENNReal.ofReal_mul hwR.le, ← mul_assoc, ENNReal.inv_mul_cancel, one_mul]
      · rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hwR
      · exact ENNReal.ofReal_ne_top
    · rw [if_neg h] at hmul
      have h0 : chainPMF (condRule p w) j u = 0 := by
        rcases mul_eq_zero.mp hmul with h1 | h1
        · exact absurd h1 hw.ne'
        · exact h1
      rw [h0]; simp

/-- **5a for Soto's extrapolation**: conditioning `extrapolate S e q` on a written-out level-`k`
conjunction of positive mass re-runs the chain from that state with the same clauses beyond it.
Source: PIBBSS §4.3 p. 18 ("conditioned on … the complete state description of a state
`Q_{k+n} = Q`, it nicely extrapolates its finite beliefs into the infinite automatically")
Kind: C
Fidelity: variant: `Future` clause dropped; the conditioning event is a level-`k` conjunction
Hyps: (a) `0 ≤ q`; (a) `0 < sotoPMF S e q k w` -/
theorem extrapolate_cond_cylinder (S : UnivStructure) [∀ Γ φ, Decidable (AxEntails S Γ φ)]
    (e : ℕ ≃ ℕ) {B : ℕ} (q : FiniteWorld B → ℚ) (hq0 : ∀ w, 0 ≤ q w) {k : ℕ} (w : FiniteWorld k)
    (hw : 0 < sotoPMF S e q k w) :
    (extrapolate S e q hq0)[|cyl e w] =
      chainMeasure e (condRule (sotoRule S e q) w) (condRule_inUnit (sotoRule_inUnit S e hq0) w) :=
  chainMeasure_cond_cylinder e (sotoRule_inUnit S e hq0) w hw

/-! ## 5b — constraint 2 and exact introspection are definitional -/

/-- Two rules agreeing below level `n` have the same chain at level `n`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma chainPMF_congr_below {p p' : CondRule} :
    ∀ (n : ℕ), (∀ j < n, p j = p' j) → ∀ u : FiniteWorld n, chainPMF p n u = chainPMF p' n u
  | 0, _, _ => rfl
  | n + 1, h, u => by
      simp only [chainPMF]
      rw [chainPMF_congr_below n (fun j hj => h j (Nat.lt_succ_of_lt hj)) (Fin.init u),
        h n (Nat.lt_succ_self n)]

/-- Two rules agreeing below `level e φ` give `φ` the same value.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma chainVal_congr_below (e : ℕ ≃ ℕ) {p p' : CondRule} {φ : Sentence}
    (h : ∀ j < level e φ, p j = p' j) : chainVal e p φ = chainVal e p' φ := by
  unfold chainVal chainValAt
  apply Finset.sum_congr rfl
  intro u _
  rw [chainPMF_congr_below _ h u]

/-- A sentence of value zero holds only on null worlds, at any level above its own: the
world-level reading of `chainVal φ = 0` (the sum of non-negative terms is zero iff each is).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma chainPMF_eq_zero_of_chainVal_eq_zero (e : ℕ ≃ ℕ) {p : CondRule} (hp : p.InUnit)
    {φ : Sentence} {n : ℕ} (hn : level e φ ≤ n) (h : chainVal e p φ = 0) :
    ∀ u : FiniteWorld n, (enumWorld e u).toPCWorld.Holds φ → chainPMF p n u = 0 := by
  intro u hu
  rw [← chainValAt_eq_of_le e p hn] at h
  unfold chainValAt at h
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun w _ => by
    split_ifs
    · exact chainPMF_nonneg hp n w
    · exact le_rfl)).mp h u (Finset.mem_univ u)
  simpa [hu] using this

/-- Propositionally exclusive sentences have a null conjunction under every rule: the
propositional form of exclusivity implies the almost-everywhere form used below.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma chainVal_and_eq_zero_of_exclusive (e : ℕ ≃ ℕ) (p : CondRule) {φ ψ : Sentence}
    (h : ∀ v : PCWorld, ¬ (v.Holds φ ∧ v.Holds ψ)) : chainVal e p (φ ⋏ ψ) = 0 :=
  chainVal_eq_zero_of_le e p le_rfl fun _ hu => absurd ((PCWorld.holds_and _ _ _).mp hu) (h _)

/-- **The constraint-2 rule**: at the level `kφ` of the large sentence `φ` (the atom `e kφ`), the
conditional is `r` on worlds satisfying the price event `E r` (the sentence `⌜P_{n+1}(φ) = r⌝`),
for `r` in a finite grid `R`; elsewhere (and at other levels) the base rule. Written as a sum so
that the rule is total: on a world lying in exactly one cell `E r` it reads `r`; on a world in
no cell it reads `0` (a disclosed choice — the theorem below is about the cells and needs the
cells to be exclusive only on the positive-mass worlds); on a world in several cells it reads the
sum, which the exclusivity hypothesis makes irrelevant. Events are sentences, not atoms: in BLI
the price events are distinct prime sentences whose exclusivity is a property of the
*measure* (they are not propositionally exclusive), which is why exclusivity is stated as
`chainVal base (E r ⋏ E r') = 0`.
Source: PDF 06 p. 1 (`P_n("P_{n+1}(φ) = q" ∧ φ) := q · P_n("P_{n+1}(φ) = q")`);
[[bli-soto-a-2-inventory]] 005 (i)
Kind: D
Fidelity: exact (the source's display, as a rule; the off-cell default `0` is this run's) -/
def constraint2Rule (e : ℕ ≃ ℕ) (base : CondRule) (kφ : ℕ) (R : Finset ℚ) (E : ℚ → Sentence) :
    CondRule := fun k u =>
  if k = kφ then ∑ r ∈ R, if (enumWorld e u).toPCWorld.Holds (E r) then r else 0
  else base k u

/-- **5b (i), `constraint2_definitional`**: under the constraint-2 rule, for price events `E r`
(`r ∈ R`, sentences of level `≤ kφ`) that are exclusive almost everywhere under the base
(`chainVal base (E r ⋏ E r') = 0` for `r ≠ r'`), `P(E_r ∧ φ) = r · P(E_r)` for every `r ∈ R` —
BLI constraint 2 holds by definition for the large sentence `φ = atom (e kφ)`, on the whole grid
at once. The grid may have any size: `constraint2_witness` (`ConstraintWitnesses.lean`) inhabits
the package with two prices, two positive-mass cells that are exclusive only almost everywhere.
No bridge to `bli-found`'s `E2x` is claimed.
Source: PDF 06 p. 1; [[bli-soto-a-2-inventory]] 005 (i)
Kind: P
Fidelity: exact
Hyps: (a) `base.InUnit`; (a) `level e (E r) ≤ kφ`; (a) a.e. exclusivity of the price events
under the base -/
theorem constraint2_definitional (e : ℕ ≃ ℕ) {base : CondRule} (hbase : base.InUnit) (kφ : ℕ)
    (R : Finset ℚ) (E : ℚ → Sentence) (hE : ∀ r ∈ R, level e (E r) ≤ kφ)
    (hexcl : ∀ r ∈ R, ∀ r' ∈ R, r ≠ r' → chainVal e base (E r ⋏ E r') = 0)
    {r : ℚ} (hr : r ∈ R) :
    chainVal e (constraint2Rule e base kφ R E) (E r ⋏ Formula.atom (e kφ)) =
      r * chainVal e (constraint2Rule e base kφ R E) (E r) := by
  apply chainVal_and_atom e _ (hE r hr) r
  intro u hu
  have hagree : ∀ j < kφ, constraint2Rule e base kφ R E j = base j := by
    intro j hj
    funext w
    simp [constraint2Rule, hj.ne]
  rw [chainPMF_congr_below kφ hagree u]
  by_cases hu0 : chainPMF base kφ u = 0
  · exact Or.inl hu0
  right
  simp only [constraint2Rule, if_true]
  rw [Finset.sum_eq_single r]
  · simp [hu]
  · intro r' hr' hne
    rw [if_neg]
    intro hu'
    have hlev : level e (E r ⋏ E r') ≤ kφ := by simp [hE r hr, hE r' hr']
    exact hu0 (chainPMF_eq_zero_of_chainVal_eq_zero e hbase hlev (hexcl r hr r' hr' (Ne.symm hne))
      u ((PCWorld.holds_and _ _ _).mpr ⟨hu, hu'⟩))
  · intro h; exact absurd hr h

/-- **5b (i), propositional form**: the same identity when the price events are propositionally
exclusive (e.g. one-hot conjunctions over distinct atoms), which implies the a.e. form.
Source: PDF 06 p. 1; [[bli-soto-a-2-inventory]] 005 (i)
Kind: L
Fidelity: exact (a corollary of `constraint2_definitional`)
Hyps: (a) `base.InUnit`; (a) `level e (E r) ≤ kφ`; (a) propositional exclusivity -/
theorem constraint2_definitional_of_exclusive (e : ℕ ≃ ℕ) {base : CondRule} (hbase : base.InUnit)
    (kφ : ℕ) (R : Finset ℚ) (E : ℚ → Sentence) (hE : ∀ r ∈ R, level e (E r) ≤ kφ)
    (hexcl : ∀ v : PCWorld, ∀ r ∈ R, ∀ r' ∈ R, v.Holds (E r) → v.Holds (E r') → r = r')
    {r : ℚ} (hr : r ∈ R) :
    chainVal e (constraint2Rule e base kφ R E) (E r ⋏ Formula.atom (e kφ)) =
      r * chainVal e (constraint2Rule e base kφ R E) (E r) :=
  constraint2_definitional e hbase kφ R E hE
    (fun r hr r' hr' hne => chainVal_and_eq_zero_of_exclusive e base
      fun v h => hne (hexcl v r hr r' hr' h.1 h.2)) hr

/-- **When the constraint-2 rule is a rule in `[0,1]`** (so that its `chainMeasure` exists): under
*propositional* exclusivity of the price events and a grid `R ⊆ [0,1]`, the sum-form
`constraint2Rule` stays in `[0,1]` (on any world at most one cell holds, so the sum is one `r` or
`0`). Under exclusivity that is merely almost everywhere under the base this can fail: a null world
holding two cells reads the sum of their prices, which leaves `[0,1]` for grids such as `{½, ¾}`
(audit r2 adversarial §3.3's probe), so `constraint2_definitional` is then a valuation-level
identity and the constraint-2 *measure* is available only when `InUnit` is checked separately
(as `twoCellC2Rule_inUnit` does for the shipped witness, where `¼ + ¾ ≤ 1`).
Source: audit r2 adversarial §3.3; PDF 06 p. 1
Kind: L
Fidelity: exact
Hyps: (a) `base.InUnit`; (a) `R ⊆ [0,1]`; (a) propositional exclusivity -/
theorem constraint2Rule_inUnit_of_exclusive (e : ℕ ≃ ℕ) {base : CondRule} (hbase : base.InUnit)
    (kφ : ℕ) (R : Finset ℚ) (E : ℚ → Sentence) (hR : ∀ r ∈ R, 0 ≤ r ∧ r ≤ 1)
    (hexcl : ∀ v : PCWorld, ∀ r ∈ R, ∀ r' ∈ R, v.Holds (E r) → v.Holds (E r') → r = r') :
    (constraint2Rule e base kφ R E).InUnit := by
  intro k u
  unfold constraint2Rule
  split_ifs with hk
  · constructor
    · apply Finset.sum_nonneg
      intro r hr
      split_ifs
      · exact (hR r hr).1
      · exact le_rfl
    · by_cases h : ∃ r ∈ R, (enumWorld e u).toPCWorld.Holds (E r)
      · obtain ⟨r, hr, hu⟩ := h
        rw [Finset.sum_eq_single r]
        · rw [if_pos hu]; exact (hR r hr).2
        · intro r' hr' hne
          rw [if_neg]
          intro hu'
          exact hne (hexcl _ r' hr' r hr hu' hu)
        · intro h; exact absurd hr h
      · simp only [not_exists, not_and] at h
        rw [Finset.sum_eq_zero]
        · exact zero_le_one
        · intro r hr
          rw [if_neg (h r hr)]
  · exact hbase k u

/-- **The exact-introspection rule**: at the level `kq` of the quoting atom `⌜P(φ) < pr⌝`
(the atom `e kq`), the conditional is `1` if the base chain prices `φ` below `pr` and `0`
otherwise; elsewhere the base rule. Legal as a self-referential rule only when `level e φ ≤ kq`
(PDF 07's `⌜⌜φ⌝⌝ > ⌜φ⌝`): then the price of `φ` under the new rule equals the price under the
base (`chainVal_introspectionRule_eq`), so the clause refers to the rule's own price of `φ`.
Source: PDF 07 pp. 4–5 (`P(C ∧ "P(⌜φ⌝) < p") := P(C) · 1(P(φ) < p)`);
[[bli-soto-a-2-inventory]] 005 (ii)
Kind: D
Fidelity: exact (the source's display, as a rule; legality condition `level e φ ≤ kq`) -/
def introspectionRule (e : ℕ ≃ ℕ) (base : CondRule) (kq : ℕ) (φ : Sentence) (pr : ℚ) :
    CondRule := fun k u =>
  if k = kq then (if chainVal e base φ < pr then 1 else 0) else base k u

/-- Under the introspection rule the quoted sentence keeps its base price (the clause is
self-referential in the legal regime `level e φ ≤ kq`).
Source: PDF 07 p. 5 ("this will be well-defined")
Kind: L
Fidelity: exact -/
lemma chainVal_introspectionRule_eq (e : ℕ ≃ ℕ) (base : CondRule) (kq : ℕ) (φ : Sentence)
    (pr : ℚ) (hlev : level e φ ≤ kq) :
    chainVal e (introspectionRule e base kq φ pr) φ = chainVal e base φ := by
  apply chainVal_congr_below
  intro j hj
  have : j ≠ kq := by omega
  funext u
  simp [introspectionRule, this]

/-- **5b (ii), `introspection_definitional`**: under the introspection rule, for any event `E` of
level `≤ kq`, `P(E ∧ ⌜P(φ) < pr⌝) = 1[P(φ) < pr] · P(E)` where `P(φ)` is the rule's *own* price
of `φ` — exact introspection holds by definition for the large quoting atom; with `E = ⊤`,
`P(⌜P(φ) < pr⌝) = 1[P(φ) < pr]`. No bridge to `bli-found`'s `E2i` is claimed.
Source: PDF 07 pp. 4–5; [[bli-soto-a-2-inventory]] 005 (ii)
Kind: L (`chainVal_and_atom` with a constant; the content is the rule and its legality lemma
`chainVal_introspectionRule_eq`)
Fidelity: exact
Hyps: (a) `level e φ ≤ kq` (PDF 07's enumeration requirement); (a) `level e E ≤ kq` -/
theorem introspection_definitional (e : ℕ ≃ ℕ) (base : CondRule) (kq : ℕ) (φ : Sentence)
    (pr : ℚ) (hlev : level e φ ≤ kq) {E : Sentence} (hE : level e E ≤ kq) :
    chainVal e (introspectionRule e base kq φ pr) (E ⋏ Formula.atom (e kq)) =
      (if chainVal e (introspectionRule e base kq φ pr) φ < pr then 1 else 0) *
        chainVal e (introspectionRule e base kq φ pr) E := by
  rw [chainVal_introspectionRule_eq e base kq φ pr hlev]
  have hc : ∀ u : FiniteWorld kq, introspectionRule e base kq φ pr kq u =
      (if chainVal e base φ < pr then 1 else 0) := by
    intro u
    unfold introspectionRule
    rw [if_pos rfl]
  exact chainVal_and_atom e _ hE _ (fun u _ => Or.inr (hc u))

/-! ## 5c — inside the support the constraint is a condition on the base; the partition axiom -/

/-- **5c (iii), `chain_inside_support_fixed`**: for `E`, `φ` of level `≤ B`, the joint value
`extrapolateVal (E ⋏ φ)` is the base's world sum — a linear condition on `q`, not on the
extrapolation (the finding's point: the difficulty of constraint 2 for small sentences sits in
the finite base).
Source: [[bli-soto-a-2-inventory]] 005 (iii); PDF 07 p. 5 ("cannot be solved like the other cases")
Kind: L
Fidelity: exact
Hyps: (a) `0 ≤ q`, `∑ q = 1` -/
theorem chain_inside_support_fixed (S : UnivStructure) [∀ Γ φ, Decidable (AxEntails S Γ φ)]
    (e : ℕ ≃ ℕ) {B : ℕ} {q : FiniteWorld B → ℚ} (hq0 : ∀ w, 0 ≤ q w) (hq1 : ∑ w, q w = 1)
    {E φ : Sentence} (hE : level e E ≤ B) (hφ : level e φ ≤ B) :
    extrapolateVal S e q (E ⋏ φ) =
      ∑ u : FiniteWorld B, if (enumWorld e u).toPCWorld.Holds (E ⋏ φ) then q u else 0 :=
  extrapolateVal_eq_base S e hq0 hq1 (by simp [hE, hφ])

/-- A value splits along a family of events that is exclusive almost everywhere
(`chainVal (E i ⋏ E j) = 0` for `i ≠ j`) and of total value one: exclusivity plus
`∑ chainVal (E i) = 1` force every positive-mass world to lie in exactly one cell.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma chainVal_eq_sum_of_partition (e : ℕ ≃ ℕ) {p : CondRule} (hp : p.InUnit) {ι : Type*}
    [Fintype ι] (E : ι → Sentence) (φ : Sentence)
    (hexcl : ∀ i j, i ≠ j → chainVal e p (E i ⋏ E j) = 0)
    (hsum : ∑ i, chainVal e p (E i) = 1) :
    chainVal e p φ = ∑ i, chainVal e p (E i ⋏ φ) := by
  classical
  -- work at a common level
  set n := max (level e φ) (Finset.univ.sup fun i => level e (E i)) with hn
  have hφn : level e φ ≤ n := le_max_left _ _
  have hEn : ∀ i, level e (E i) ≤ n := fun i =>
    (Finset.le_sup (f := fun i => level e (E i)) (Finset.mem_univ i)).trans (le_max_right _ _)
  have hEφn : ∀ i, level e (E i ⋏ φ) ≤ n := fun i => by simp [hEn i, hφn]
  -- on a positive-mass level-`n` world two distinct cells cannot both hold
  have hexcl' : ∀ u : FiniteWorld n, chainPMF p n u ≠ 0 → ∀ i j,
      (enumWorld e u).toPCWorld.Holds (E i) → (enumWorld e u).toPCWorld.Holds (E j) → i = j := by
    intro u hu i j hi hj
    by_contra hij
    exact hu (chainPMF_eq_zero_of_chainVal_eq_zero e hp (φ := E i ⋏ E j) (by simp [hEn i, hEn j])
      (hexcl i j hij) u ((PCWorld.holds_and _ _ _).mpr ⟨hi, hj⟩))
  -- every positive-mass level-`n` world lies in some cell
  have hcover : ∀ u : FiniteWorld n, chainPMF p n u ≠ 0 →
      ∃ i, (enumWorld e u).toPCWorld.Holds (E i) := by
    intro u hu
    by_contra hnone
    simp only [not_exists] at hnone
    -- the cells' total mass would then miss `u`'s mass
    have h1 : ∑ i, chainVal e p (E i) =
        ∑ u : FiniteWorld n, (∑ i, if (enumWorld e u).toPCWorld.Holds (E i) then 1 else 0) *
          chainPMF p n u := by
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [← chainValAt_eq_of_le e p (hEn i)]
      unfold chainValAt
      apply Finset.sum_congr rfl
      intro u' _
      split_ifs <;> simp
    have hle1 : ∀ u' : FiniteWorld n, chainPMF p n u' ≠ 0 →
        (∑ i, if (enumWorld e u').toPCWorld.Holds (E i) then (1 : ℚ) else 0) ≤ 1 := by
      intro u' hu'
      by_cases h : ∃ i, (enumWorld e u').toPCWorld.Holds (E i)
      · obtain ⟨i, hi⟩ := h
        rw [Finset.sum_eq_single i]
        · simp [hi]
        · intro j _ hj
          rw [if_neg]
          intro hj'
          exact hj (hexcl' u' hu' j i hj' hi)
        · intro h; exact absurd (Finset.mem_univ i) h
      · simp only [not_exists] at h
        simp [h]
    have hlt : ∑ u' : FiniteWorld n, (∑ i, if (enumWorld e u').toPCWorld.Holds (E i) then (1 : ℚ)
        else 0) * chainPMF p n u' < ∑ u' : FiniteWorld n, chainPMF p n u' := by
      apply Finset.sum_lt_sum
      · intro u' _
        by_cases hu' : chainPMF p n u' = 0
        · rw [hu', mul_zero]
        calc (∑ i, if (enumWorld e u').toPCWorld.Holds (E i) then (1 : ℚ) else 0) *
              chainPMF p n u'
            ≤ 1 * chainPMF p n u' :=
              mul_le_mul_of_nonneg_right (hle1 u' hu') (chainPMF_nonneg hp n u')
          _ = chainPMF p n u' := one_mul _
      · refine ⟨u, Finset.mem_univ u, ?_⟩
        have : (∑ i, if (enumWorld e u).toPCWorld.Holds (E i) then (1 : ℚ) else 0) = 0 := by
          simp [hnone]
        rw [this, zero_mul]
        exact lt_of_le_of_ne (chainPMF_nonneg hp n u) (Ne.symm hu)
    rw [← h1, hsum, chainPMF_sum_one] at hlt
    exact lt_irrefl _ hlt
  -- termwise identity at level `n`
  rw [← chainValAt_eq_of_le e p hφn]
  have : ∀ i, chainVal e p (E i ⋏ φ) = chainValAt e p n (E i ⋏ φ) := fun i =>
    (chainValAt_eq_of_le e p (hEφn i)).symm
  simp only [this]
  unfold chainValAt
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu : chainPMF p n u = 0
  · simp [hu]
  · obtain ⟨i, hi⟩ := hcover u hu
    rw [Finset.sum_eq_single i]
    · simp [PCWorld.holds_and, hi]
    · intro j _ hj
      rw [if_neg]
      rw [PCWorld.holds_and]
      rintro ⟨hj', _⟩
      exact hj (hexcl' u hu j i hj' hi)
    · intro h; exact absurd (Finset.mem_univ i) h

/-- **5c (iv), `partition_gives_balance`**: from a partition of unity `∑ chainVal (E i) = 1` (the
partition axiom) over cells that are exclusive almost everywhere (`chainVal (E i ⋏ E j) = 0`
for `i ≠ j` — the form the BLI price events have, not being propositionally exclusive) and
constraint 2 on each cell (`chainVal (E i ⋏ φ) = r i · chainVal (E i)`),
`chainVal φ = ∑ r i · chainVal (E i)` — BLI constraint 4 from constraint 2 plus the partition
axiom. Propositional exclusivity gives the a.e. form through `chainVal_and_eq_zero_of_exclusive`.
Inhabited by `constraint2_witness` (two a.e.-exclusive atoms of masses `1/3`, `2/3`).
Source: [[bli-soto-a-2-inventory]] 005 (iv); bli-soto-a-006 (constraint 4 ⟺ partition axiom)
Kind: L
Fidelity: exact
Hyps: (a) a.e. exclusivity; (a) partition of unity; (a) constraint 2 on each cell -/
theorem partition_gives_balance (e : ℕ ≃ ℕ) {p : CondRule} (hp : p.InUnit) {ι : Type*}
    [Fintype ι] (E : ι → Sentence) (φ : Sentence) (r : ι → ℚ)
    (hexcl : ∀ i j, i ≠ j → chainVal e p (E i ⋏ E j) = 0)
    (hsum : ∑ i, chainVal e p (E i) = 1)
    (hcond : ∀ i, chainVal e p (E i ⋏ φ) = r i * chainVal e p (E i)) :
    chainVal e p φ = ∑ i, r i * chainVal e p (E i) := by
  rw [chainVal_eq_sum_of_partition e hp E φ hexcl hsum]
  exact Finset.sum_congr rfl fun i _ => hcond i

end Cleanroom.Bli.BliExtrapolation
