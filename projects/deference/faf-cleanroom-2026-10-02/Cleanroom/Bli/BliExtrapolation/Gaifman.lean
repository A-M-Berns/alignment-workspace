import Cleanroom.Bli.BliExtrapolation.Soto

/-!
# `bli-extrapolation` · Gaifman: the static Gaifman property of Soto's extrapolation (target 4;
design decision 7)

Fix `S`, `e`, a base `q` (nonnegative, mass one, `Ax`-consistent) and a universal `u`. Write
`μ := extrapolate S e q`, `U := univSentence u`, `I_i := {v | v ⊨ inst u i}`. The sources claim
`P(∀mφ(m)) = lim_m P(⋀_{i≤m} φ(i))`. Here (**limits are measure limits**, decision 7: the limit is
the measure of the intersection, by continuity from above — exactly what a finitely additive
content lacks):

* **4a** `gaifman_le`: `μ U ≤ μ (⋂ i, I_i)` unconditionally (schema 1 holds a.e.), with the finite
  form and `tendsto_conj_instances`.
* **4d** `gaifman_lt_of_hiddenUniversal`: if some conjunction of positive mass refutes `U` yet
  `Ax`-entails every instance (`HiddenUniversal`), then `μ U < μ (⋂ i, I_i)` **strictly** — the
  obstruction theorem; the 2-006 witness (`Witnesses.lean`) refutes the sources' unconditional
  `≥`.
* **4b** `gaifman_eq_of_halving`: under `HalvingCondition` — infinitely many instances are fresh
  atoms at increasing levels that no `Ax`-consistent `¬U`-conjunction below them decides — the
  identity holds: Soto's halving argument, made true by naming the condition it needs.
* **4e** `halving_of_fresh_instances`: a syntactic sufficient condition for `HalvingCondition`.
* **4c(i)** `tendsto_first_counterexample`: the "first counterexample" events are disjoint, so
  their measures tend to `0` for *any* finite measure — PDF 06 footnote 1's hypothesis is idle.

`HalvingCondition`, `HiddenUniversal` and the obstruction theorem are this run's, not Soto's.

Sources: PDF 07 p. 2; PIBBSS §4.3 p. 18; PDF 06 p. 2 and footnote 1; [[bli-soto-a-inventory]] 052;
[[bli-soto-a-2-inventory]] 006; [[bli-soto-b-inventory]] 033 (iii) and its flag.
-/

namespace Cleanroom.Bli.BliExtrapolation

open LogicalInduction LO.Propositional BoolPCWorld MeasureTheory Filter Topology Finset Function

/-! ## Events -/

/-- The event "the universal sentence of `u` holds".
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def univEvent (S : UnivStructure) (u : ℕ) : Set BoolPCWorld :=
  {v | v.toPCWorld.Holds (S.univSentence u)}

/-- The event "the `i`-th instance of `u` holds".
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def instEvent (S : UnivStructure) (u i : ℕ) : Set BoolPCWorld :=
  {v | v.toPCWorld.Holds (S.inst u i)}

/-- `univEvent` is measurable.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma measurableSet_univEvent (S : UnivStructure) (u : ℕ) : MeasurableSet (univEvent S u) :=
  measurableSet_holds _

/-- `instEvent` is measurable.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma measurableSet_instEvent (S : UnivStructure) (u i : ℕ) : MeasurableSet (instEvent S u i) :=
  measurableSet_holds _

/-- The intersection of all instance events is measurable.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma measurableSet_iInter_instEvent (S : UnivStructure) (u : ℕ) :
    MeasurableSet (⋂ i, instEvent S u i) :=
  MeasurableSet.iInter fun i => measurableSet_instEvent S u i

/-- Finite intersections of instance events are measurable.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma measurableSet_biInter_instEvent (S : UnivStructure) (u m : ℕ) :
    MeasurableSet (⋂ i ≤ m, instEvent S u i) :=
  MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ => measurableSet_instEvent S u i

section Gaifman

variable (S : UnivStructure) [∀ Γ φ, Decidable (AxEntails S Γ φ)] (e : ℕ ≃ ℕ) {B : ℕ}

/-! ## 4a — the `≤` inequality -/

/-- Almost everywhere, the universal implies each of its instances (schema 1 a.e., from
`extrapolate_ae_Ax`).
Source: PDF 07 p. 2 ("`Ax` ensures …")
Kind: L
Fidelity: n/a -/
theorem univ_ae_imp_inst (q : FiniteWorld B → ℚ) (u : ℕ) (hq0 : ∀ w, 0 ≤ q w) (hq1 : ∑ w, q w = 1)
    (hbase : BaseAxConsistent S e q) :
    ∀ᵐ v ∂extrapolate S e q hq0,
      v.toPCWorld.Holds (S.univSentence u) → ∀ i, v.toPCWorld.Holds (S.inst u i) := by
  filter_upwards [extrapolate_ae_Ax S e hq0 hq1 hbase] with v hv hU i
  exact hv _ (Or.inl (Or.inl ⟨u, i, rfl⟩)) hU

/-- `univEvent ⊆ ⋂ instEvent` almost everywhere.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem univEvent_ae_le_iInter (q : FiniteWorld B → ℚ) (u : ℕ) (hq0 : ∀ w, 0 ≤ q w) (hq1 : ∑ w, q w = 1)
    (hbase : BaseAxConsistent S e q) :
    univEvent S u ≤ᵐ[extrapolate S e q hq0] ⋂ i, instEvent S u i := by
  filter_upwards [univ_ae_imp_inst S e q u hq0 hq1 hbase] with v hv hU
  exact Set.mem_iInter.mpr (hv hU)

/-- **4a, `gaifman_le`** (the `≤` inequality, unconditionally): the measure of the universal is at
most the measure of the intersection of all its instances. Stated over an abstract quantifier
structure `S` (decision 1) and an enumeration `e` (decision 3); the measure is FAF's
`gaifmanMeasure` of the chained valuation (decision 4, route α). **The limit is the measure of
the intersection** (decision 7; `tendsto_conj_instances` supplies the `Tendsto` form); a finitely
additive content has no such limit statement.
Source: PDF 07 p. 2 ("`Ax` ensures `P(∀mφ(m)) ≤ lim_m P(⋀ φ(i))`"); PIBBSS §4.3 p. 18;
[[bli-soto-a-inventory]] 052 (i); PDF 06 p. 2 ("we'd already have the `≤` inequality by default")
Kind: P
Fidelity: exact
Hyps: (a) `0 ≤ q`, `∑ q = 1`; (a) `BaseAxConsistent S e q` (discharged by every witness) -/
theorem gaifman_le (q : FiniteWorld B → ℚ) (u : ℕ) (hq0 : ∀ w, 0 ≤ q w) (hq1 : ∑ w, q w = 1)
    (hbase : BaseAxConsistent S e q) :
    extrapolate S e q hq0 (univEvent S u) ≤ extrapolate S e q hq0 (⋂ i, instEvent S u i) :=
  measure_mono_ae (univEvent_ae_le_iInter S e q u hq0 hq1 hbase)

/-- **4a, finite form**: `μ U ≤ μ (⋂ i ≤ m, I_i)` for every `m`.
Source: PDF 07 p. 2; PIBBSS §4.3 p. 18 ("in all worlds where the former is true, the latter also is")
Kind: P
Fidelity: exact
Hyps: (a) as `gaifman_le` -/
theorem gaifman_le_finite (q : FiniteWorld B → ℚ) (u : ℕ) (hq0 : ∀ w, 0 ≤ q w) (hq1 : ∑ w, q w = 1)
    (hbase : BaseAxConsistent S e q) (m : ℕ) :
    extrapolate S e q hq0 (univEvent S u) ≤ extrapolate S e q hq0 (⋂ i ≤ m, instEvent S u i) := by
  apply measure_mono_ae
  filter_upwards [univ_ae_imp_inst S e q u hq0 hq1 hbase] with v hv hU
  show v ∈ ⋂ i ≤ m, instEvent S u i
  simp only [Set.mem_iInter]
  intro i _
  exact hv hU i

/-- **The limit exists and is the measure of the intersection** (`tendsto_conj_instances`;
decision 7): `μ (⋂ i ≤ m, I_i) → μ (⋂ i, I_i)` as `m → ∞`, by continuity from above
(`tendsto_measure_iInter_atTop`; the sets are antitone and measurable, the measure finite). This
is also [[bli-soto-a-inventory]] 052 (iii) ("the limit exists (monotone, bounded)") — no separate
declaration. Holds for any base (no `Ax`-consistency needed).
Source: PDF 06 p. 2 ("their limit will exist"); PDF 07 p. 2; [[bli-soto-a-inventory]] 052 (iii)
Kind: P
Fidelity: exact
Hyps: (a) `0 ≤ q` -/
theorem tendsto_conj_instances (q : FiniteWorld B → ℚ) (u : ℕ) (hq0 : ∀ w, 0 ≤ q w) :
    Tendsto (fun m => extrapolate S e q hq0 (⋂ i ≤ m, instEvent S u i)) atTop
      (𝓝 (extrapolate S e q hq0 (⋂ i, instEvent S u i))) := by
  have hanti : Antitone (fun m => ⋂ i ≤ m, instEvent S u i) := by
    intro m m' hmm' v hv
    simp only [Set.mem_iInter] at hv ⊢
    intro i hi
    exact hv i (hi.trans hmm')
  have h := tendsto_measure_iInter_atTop (μ := extrapolate S e q hq0)
    (s := fun m => ⋂ i ≤ m, instEvent S u i)
    (fun m => (measurableSet_biInter_instEvent S u m).nullMeasurableSet) hanti
    ⟨0, measure_ne_top _ _⟩
  have heq : (⋂ m, ⋂ i ≤ m, instEvent S u i) = ⋂ i, instEvent S u i := by
    ext v
    simp only [Set.mem_iInter]
    exact ⟨fun h i => h i i le_rfl, fun h m i _ => h i⟩
  rw [heq] at h
  exact h

/-! ## The decomposition `μ (⋂ I_i) = μ U + μ (¬U ∧ ⋂ I_i)` -/

/-- The measure of the intersection of the instances splits as the measure of the universal
plus the measure of "`¬U` and all instances" (from `gaifman_le`'s a.e. inclusion).
Source: none: infrastructure (the arithmetic of PDF 07 p. 2's argument)
Kind: L
Fidelity: n/a -/
theorem measure_iInter_instEvent_eq (q : FiniteWorld B → ℚ) (u : ℕ) (hq0 : ∀ w, 0 ≤ q w) (hq1 : ∑ w, q w = 1)
    (hbase : BaseAxConsistent S e q) :
    extrapolate S e q hq0 (⋂ i, instEvent S u i) =
      extrapolate S e q hq0 (univEvent S u) +
        extrapolate S e q hq0 ((univEvent S u)ᶜ ∩ ⋂ i, instEvent S u i) := by
  have h := measure_inter_add_sdiff (μ := extrapolate S e q hq0) (⋂ i, instEvent S u i)
    (measurableSet_univEvent S u)
  rw [Set.sdiff_eq, Set.inter_comm _ (univEvent S u)ᶜ] at h
  rw [← h]
  congr 1
  apply le_antisymm (measure_mono Set.inter_subset_right)
  apply measure_mono_ae
  filter_upwards [univEvent_ae_le_iInter S e q u hq0 hq1 hbase] with v hv hU
  exact ⟨hv hU, hU⟩

/-! ## 4d — the obstruction theorem -/

/-- **Hidden universal** (this run's name for the hypothesis of the obstruction theorem): some
level-`k` conjunction `w` of positive chained mass refutes `U` (`U`'s atom is below level `k` and
`w` reads it against `U`) yet `Ax`-entails every instance of `u`. Not a property of `μ`: it is a
statement about the rule (`sotoPMF`) and about entailment.
Source: [[bli-soto-a-2-inventory]] 006 (the mechanism); PDF 07 p. 2 ("could only fail if a
finite and `Ax`-consistent `C ∧ ¬∀mφ(m)` propositionally entailed infinitely many `φ(i)`")
Kind: D
Fidelity: exact (the source's own failure condition, named) -/
def HiddenUniversal (q : FiniteWorld B → ℚ) (u : ℕ) : Prop :=
  ∃ (k : ℕ) (w : FiniteWorld k), 0 < sotoPMF S e q k w ∧
    level e (S.univSentence u) ≤ k ∧ ¬ (enumWorld e w).toPCWorld.Holds (S.univSentence u) ∧
    ∀ i, AxEntails S {conj e w} (S.inst u i)

/-- **The mass of a hidden conjunction bounds the failure**: if the level-`k` conjunction `w`
refutes `U` (`U`'s level `≤ k`) and `Ax`-entails every instance, then the event "`¬U` and every
instance" has measure at least `ofReal (sotoPMF k w)` (the cylinder of `w` lies in it a.e.).
Source: PDF 07 p. 2 (the source's own failure condition)
Kind: P
Fidelity: exact
Hyps: (a) `0 ≤ q`, `∑ q = 1`, `BaseAxConsistent S e q` -/
theorem hidden_le_measure (q : FiniteWorld B → ℚ) (u : ℕ) (hq0 : ∀ w, 0 ≤ q w)
    (hq1 : ∑ w, q w = 1) (hbase : BaseAxConsistent S e q) (k : ℕ) (w : FiniteWorld k)
    (hlev : level e (S.univSentence u) ≤ k)
    (hnU : ¬ (enumWorld e w).toPCWorld.Holds (S.univSentence u))
    (hent : ∀ i, AxEntails S {conj e w} (S.inst u i)) :
    ENNReal.ofReal (sotoPMF S e q k w) ≤
      extrapolate S e q hq0 ((univEvent S u)ᶜ ∩ ⋂ i, instEvent S u i) := by
  have hsub : cyl e w ≤ᵐ[extrapolate S e q hq0]
      (((univEvent S u)ᶜ ∩ ⋂ i, instEvent S u i : Set BoolPCWorld)) := by
    filter_upwards [extrapolate_ae_Ax S e hq0 hq1 hbase] with v hv hw
    have hw' : v.toPCWorld.Holds (conj e w) := hw
    refine ⟨?_, Set.mem_iInter.mpr fun i => ?_⟩
    · show ¬ v.toPCWorld.Holds (S.univSentence u)
      rw [holds_congr_of_holds_conj_pc e hlev hw']
      exact hnU
    · exact hent i v.toPCWorld hv (fun φ hφ => by
        rw [Finset.mem_singleton] at hφ; subst hφ; exact hw')
  have := measure_mono_ae hsub
  unfold extrapolate at this ⊢
  rwa [chainMeasure_conj] at this

/-- **4d, the obstruction theorem** (load-bearing): under `HiddenUniversal`, the measure of
"`¬U` and all instances" is at least the positive mass of the hidden conjunction, hence
`μ U < μ (⋂ i, I_i)` **strictly** — the sources' second inequality fails. Stated over an abstract
quantifier structure `S` (decision 1) and an enumeration `e` (decision 3); the measure is FAF's
`gaifmanMeasure` of the chained valuation (decision 4, route α); the limit is the measure of the
intersection (decision 7). The witnesses `refute_second_inequality` (2-006) and
`refute_propagation` (057(ii)) in `Refutations.lean` inhabit the hypothesis with positive base mass.
Source: PDF 07 p. 2 / PIBBSS §4.3 p. 18 ("We also get the other inequality … This isn't possible
with our `Ax`, because the only way to have this is through quantification") — refuted;
[[bli-soto-a-2-inventory]] 006
Kind: P
Fidelity: exact (refutation of the unconditional `≥` under the abstract layer; the first-order
version is target 8's)
Hyps: (a) `0 ≤ q`, `∑ q = 1`, `BaseAxConsistent S e q`; (a) `HiddenUniversal` (discharged by the
two witnesses) -/
theorem gaifman_lt_of_hiddenUniversal (q : FiniteWorld B → ℚ) (u : ℕ) (hq0 : ∀ w, 0 ≤ q w)
    (hq1 : ∑ w, q w = 1) (hbase : BaseAxConsistent S e q)
    (h : HiddenUniversal S e q u) :
    extrapolate S e q hq0 (univEvent S u) < extrapolate S e q hq0 (⋂ i, instEvent S u i) := by
  obtain ⟨k, w, hpos, hlev, hnU, hent⟩ := h
  have h1 := hidden_le_measure S e q u hq0 hq1 hbase k w hlev hnU hent
  rw [measure_iInter_instEvent_eq S e q u hq0 hq1 hbase]
  calc extrapolate S e q hq0 (univEvent S u)
      < extrapolate S e q hq0 (univEvent S u) + ENNReal.ofReal (sotoPMF S e q k w) := by
        apply ENNReal.lt_add_right (measure_ne_top _ _)
        rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
        exact_mod_cast hpos
    _ ≤ _ := by gcongr

/-! ## 4b — the identity under the halving condition -/

/-- **Halving condition** (this run's name for what Soto's argument needs): there are strictly
increasing levels `k n ≥ B` (with `U`'s atom below `k 0`) and instance indices `i n` such that the
`i n`-th instance is the atom `e (k n)` at level `k n`, and no `Ax`-consistent level-`k n`
conjunction refuting `U` decides that atom either way. Plain words: infinitely many instances are
fresh atoms at increasing levels that no `Ax`-consistent `¬U`-conjunction below them decides. A
statement about the rule (entailment from `¬U`-conjunctions at named levels), not about `μ`.
Source: PDF 07 p. 2 / PIBBSS §4.3 p. 18 ("the Agnostic clause will be triggered infinite times");
[[bli-soto-b-inventory]] 033 (iii) and its flag
Kind: D
Fidelity: n/a (this run's condition) -/
def HalvingCondition (B : ℕ) (u : ℕ) : Prop :=
  ∃ (k : ℕ → ℕ) (i : ℕ → ℕ), StrictMono k ∧ B ≤ k 0 ∧ level e (S.univSentence u) ≤ k 0 ∧
    (∀ n, S.inst u (i n) = Formula.atom (e (k n))) ∧
    ∀ n (w : FiniteWorld (k n)), AxConsistent S {conj e w} →
      ¬ (enumWorld e w).toPCWorld.Holds (S.univSentence u) →
      ¬ AxEntails S {conj e w} (Formula.atom (e (k n))) ∧
        ¬ AxEntails S {conj e w} (∼Formula.atom (e (k n)))

/-- `∼U ∧ a 0 ∧ … ∧ a (n-1)`, built left-nested so that each step is one `chainVal_and_atom`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def negUnivPrefix (U : Sentence) (a : ℕ → ℕ) : ℕ → Sentence
  | 0 => ∼U
  | n + 1 => negUnivPrefix U a n ⋏ Formula.atom (a n)

/-- `negUnivPrefix` implies `∼U`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma negUnivPrefix_imp_neg (U : Sentence) (a : ℕ → ℕ) (v : PCWorld) :
    ∀ n, v.Holds (negUnivPrefix U a n) → v.Holds (∼U)
  | 0, h => h
  | n + 1, h => negUnivPrefix_imp_neg U a v n ((PCWorld.holds_and _ _ _).mp h).1

/-- The level of `negUnivPrefix U (e ∘ k) n` is at most `k n` when `k` is strictly increasing and
`U`'s level is at most `k 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma level_negUnivPrefix (U : Sentence) (k : ℕ → ℕ) (hk : StrictMono k)
    (hlev : level e U ≤ k 0) : ∀ n, level e (negUnivPrefix U (fun n => e (k n)) n) ≤ k n
  | 0 => by simpa [negUnivPrefix] using hlev
  | n + 1 => by
      simp only [negUnivPrefix, level_and, level_atom, Equiv.symm_apply_apply, max_le_iff]
      exact ⟨(level_negUnivPrefix U k hk hlev n).trans (hk (Nat.lt_succ_self n)).le,
        hk (Nat.lt_succ_self n)⟩

/-- Under `HalvingCondition`, each level `k n` halves the mass of `¬U ∧ (instances so far)`.
Source: PIBBSS §4.3 p. 18 ("the infinite multiplication by 1/2")
Kind: P
Fidelity: exact -/
theorem negUnivPrefix_val_succ (q : FiniteWorld B → ℚ) (u : ℕ) (hq0 : ∀ w, 0 ≤ q w) (hq1 : ∑ w, q w = 1)
    (hbase : BaseAxConsistent S e q) (k : ℕ → ℕ) (hk : StrictMono k) (hkB : B ≤ k 0)
    (hlev : level e (S.univSentence u) ≤ k 0)
    (hhalf : ∀ n (w : FiniteWorld (k n)), AxConsistent S {conj e w} →
      ¬ (enumWorld e w).toPCWorld.Holds (S.univSentence u) →
      ¬ AxEntails S {conj e w} (Formula.atom (e (k n))) ∧
        ¬ AxEntails S {conj e w} (∼Formula.atom (e (k n)))) (n : ℕ) :
    extrapolateVal S e q (negUnivPrefix (S.univSentence u) (fun n => e (k n)) (n + 1)) =
      (1 / 2) * extrapolateVal S e q (negUnivPrefix (S.univSentence u) (fun n => e (k n)) n) := by
  unfold extrapolateVal
  show chainVal e (sotoRule S e q) (negUnivPrefix (S.univSentence u) (fun n => e (k n)) n ⋏
    Formula.atom (e (k n))) = _
  apply chainVal_and_atom e _ (level_negUnivPrefix e _ k hk hlev n) (1 / 2)
  intro w hw
  by_cases hc : AxConsistent S {conj e w}
  · right
    rw [sotoRule_of_le S e q (hkB.trans (hk.monotone (Nat.zero_le n))) w]
    have hnU : ¬ (enumWorld e w).toPCWorld.Holds (S.univSentence u) :=
      (PCWorld.holds_neg _ _).mp (negUnivPrefix_imp_neg _ _ _ n hw)
    obtain ⟨h1, h2⟩ := hhalf n w hc hnU
    simp [axClause, h1, h2]
  · left
    exact sotoPMF_zero_of_inconsistent S e hq0 hq1 hbase _ w hc

/-- **4b, `gaifman_eq_of_halving`** (load-bearing): under `HalvingCondition`,
`μ U = μ (⋂ i, I_i)`. Proof: `μ (¬U ∧ ⋂ I_i) = 0`, because at each level `k n` the mass of
`¬U ∧ (instances so far)` is multiplied by exactly `½` (`chainVal_and_atom`: every `Ax`-consistent
`¬U`-conjunction gets the agnostic clause, the inconsistent ones are null), so it is
`≤ 2^{-n} · μ(¬U)` and the intersection is null; then `measure_iInter_instEvent_eq`. This is
Soto's argument, made true by naming the condition it needs. Stated over an abstract quantifier
structure `S` (decision 1) and an enumeration `e` (decision 3); the measure is FAF's
`gaifmanMeasure` of the chained valuation (decision 4, route α); the limit is the measure of the
intersection (decision 7).
Source: PDF 07 p. 2 / PIBBSS §4.3 p. 18 ("the agnostic clause will be triggered infinite times,
and the infinite multiplication by 1/2 drives the limit to 0"); [[bli-soto-b-inventory]] 033 (iii)
and its flag; [[bli-soto-a-inventory]] 052 (v)
Kind: P
Fidelity: weaker: under `HalvingCondition` (the source claims it unconditionally; see
`refute_second_inequality`)
Hyps: (a) `0 ≤ q`, `∑ q = 1`; (a) `BaseAxConsistent S e q` (discharged by `halving_witness`);
(a) `HalvingCondition` (discharged by `halving_witness`, and by `halving_of_fresh_instances` for
any fresh-instance structure) -/
theorem gaifman_eq_of_halving (q : FiniteWorld B → ℚ) (u : ℕ) (hq0 : ∀ w, 0 ≤ q w) (hq1 : ∑ w, q w = 1)
    (hbase : BaseAxConsistent S e q)
    (h : HalvingCondition S e B u) :
    extrapolate S e q hq0 (univEvent S u) = extrapolate S e q hq0 (⋂ i, instEvent S u i) := by
  obtain ⟨k, i, hk, hkB, hlev, hinst, hhalf⟩ := h
  set ψ := negUnivPrefix (S.univSentence u) (fun n => e (k n)) with hψ
  have hval : ∀ n, extrapolateVal S e q (ψ n) = (1 / 2) ^ n * extrapolateVal S e q (ψ 0) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [hψ, negUnivPrefix_val_succ S e q u hq0 hq1 hbase k hk hkB hlev hhalf n, ← hψ, ih]
        ring
  have hN : ∀ n, (univEvent S u)ᶜ ∩ ⋂ i, instEvent S u i ⊆ {v | v.toPCWorld.Holds (ψ n)} := by
    intro n
    induction n with
    | zero =>
        rintro v ⟨hvU, _⟩
        exact (PCWorld.holds_neg _ _).mpr hvU
    | succ n ih =>
        rintro v ⟨hvU, hvI⟩
        refine (PCWorld.holds_and _ _ _).mpr ⟨ih ⟨hvU, hvI⟩, ?_⟩
        have := Set.mem_iInter.mp hvI (i n)
        show v.toPCWorld.Holds (Formula.atom (e (k n)))
        rw [← hinst n]
        exact this
  have hzero : extrapolate S e q hq0 ((univEvent S u)ᶜ ∩ ⋂ i, instEvent S u i) = 0 := by
    apply le_antisymm _ zero_le
    have hle : ∀ n, extrapolate S e q hq0 ((univEvent S u)ᶜ ∩ ⋂ i, instEvent S u i) ≤
        ENNReal.ofReal ((1 / 2 : ℝ) ^ n * (extrapolateVal S e q (ψ 0) : ℝ)) := by
      intro n
      calc extrapolate S e q hq0 ((univEvent S u)ᶜ ∩ ⋂ i, instEvent S u i)
          ≤ extrapolate S e q hq0 {v | v.toPCWorld.Holds (ψ n)} := measure_mono (hN n)
        _ = ENNReal.ofReal (extrapolateVal S e q (ψ n)) := extrapolate_sentence S e hq0 _
        _ = ENNReal.ofReal ((1 / 2 : ℝ) ^ n * (extrapolateVal S e q (ψ 0) : ℝ)) := by
            rw [hval n]; push_cast; rfl
    have htend : Tendsto (fun n => ENNReal.ofReal ((1 / 2 : ℝ) ^ n *
        (extrapolateVal S e q (ψ 0) : ℝ))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n => (1 / 2 : ℝ) ^ n * (extrapolateVal S e q (ψ 0) : ℝ)) atTop
          (𝓝 (0 * (extrapolateVal S e q (ψ 0) : ℝ))) :=
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).mul_const _
      rw [zero_mul] at h1
      have h2 := ENNReal.tendsto_ofReal h1
      rwa [ENNReal.ofReal_zero] at h2
    exact ge_of_tendsto' htend hle
  rw [measure_iInter_instEvent_eq S e q u hq0 hq1 hbase, hzero, add_zero]

/-! ## 4e — a syntactic sufficient condition -/

/-- **Fresh instances**: the instances of `u` are the atoms `e (k n)` for strictly increasing levels
`k n ≥ B` beyond `U`'s level, and no axiom of `Ax S` other than `U 🡒 inst u n` mentions the atom
`e (k n)`.
Source: none: this run's condition (the honest general sufficient condition for
`HalvingCondition`)
Kind: D
Fidelity: n/a -/
def FreshInstances (B : ℕ) (u : ℕ) : Prop :=
  ∃ k : ℕ → ℕ, StrictMono k ∧ B ≤ k 0 ∧ level e (S.univSentence u) ≤ k 0 ∧
    (∀ n, S.inst u n = Formula.atom (e (k n))) ∧
    ∀ n, ∀ a ∈ Ax S, e (k n) ∈ sentenceAtomCodes a → a = S.univSentence u 🡒 S.inst u n

omit [∀ Γ φ, Decidable (AxEntails S Γ φ)] in
/-- **A fresh instance atom is undecided by `¬U`-conjunctions**: if `U`'s level is `≤ m` and no
axiom other than `U 🡒 inst u n` mentions the atom `e m`, then no `Ax`-consistent level-`m`
conjunction refuting `U` entails either literal on `e m`. Proof: take a world witnessing the
conjunction's consistency and flip the atom `e m` either way; the flipped world still satisfies
`Ax` (the only axiom mentioning that atom has a refuted antecedent) and the conjunction.
Source: none: this run's lemma (the content of 4e)
Kind: P
Fidelity: n/a -/
theorem fresh_undecided (u m n : ℕ) (hlev : level e (S.univSentence u) ≤ m)
    (hfresh : ∀ a ∈ Ax S, e m ∈ sentenceAtomCodes a → a = S.univSentence u 🡒 S.inst u n)
    (w : FiniteWorld m) (hc : AxConsistent S {conj e w})
    (hnU : ¬ (enumWorld e w).toPCWorld.Holds (S.univSentence u)) :
    ¬ AxEntails S {conj e w} (Formula.atom (e m)) ∧
      ¬ AxEntails S {conj e w} (∼Formula.atom (e m)) := by
  have hne : S.univ u ≠ e m := by
    intro heq
    have := (level_le_iff e _ _).mp hlev (S.univ u) (by simp)
    rw [heq, Equiv.symm_apply_apply] at this
    exact lt_irrefl _ this
  have key : ∀ b : Bool, ∃ v : PCWorld, AxHolds S v ∧ v.ConsistentWith {conj e w} ∧
      (v (e m) ↔ b = true) := by
    intro b
    obtain ⟨v₀, hv₀, hΓ₀⟩ := hc
    have hconj₀ : v₀.Holds (conj e w) := hΓ₀ _ (Finset.mem_singleton_self _)
    refine ⟨fun a => if a = e m then (b = true) else v₀ a, ?_, ?_, ?_⟩
    · intro a ha
      by_cases hmem : e m ∈ sentenceAtomCodes a
      · rw [hfresh a ha hmem]
        intro hU
        exfalso
        have hagree : (v₀.Holds (S.univSentence u) ↔
            PCWorld.Holds (fun a => if a = e m then (b = true) else v₀ a)
              (S.univSentence u)) := by
          apply PCWorld.holds_congr_atomCodes
          intro c hc
          simp only [UnivStructure.sentenceAtomCodes_univSentence, Finset.mem_singleton] at hc
          subst hc
          simp [hne]
        have hv₀U : ¬ v₀.Holds (S.univSentence u) := by
          rw [holds_congr_of_holds_conj_pc e hlev hconj₀]
          exact hnU
        exact hv₀U (hagree.mpr hU)
      · have hagree : (v₀.Holds a ↔
            PCWorld.Holds (fun a => if a = e m then (b = true) else v₀ a) a) := by
          apply PCWorld.holds_congr_atomCodes
          intro c hc
          have : c ≠ e m := fun h => hmem (h ▸ hc)
          simp [this]
        exact hagree.mp (hv₀ a ha)
    · intro φ hφ
      rw [Finset.mem_singleton] at hφ
      subst hφ
      rw [conj_holds_iff] at hconj₀ ⊢
      intro j
      rw [← hconj₀ j]
      have : e j ≠ e m := by
        intro h
        have := e.injective h
        have hj := j.2
        omega
      simp [this]
    · simp
  constructor
  · intro hent
    obtain ⟨v, hv, hΓ, hvb⟩ := key false
    have := hent v hv hΓ
    rw [PCWorld.holds_atom] at this
    simp only [Bool.false_eq_true, iff_false] at hvb
    exact hvb this
  · intro hent
    obtain ⟨v, hv, hΓ, hvb⟩ := key true
    have := hent v hv hΓ
    rw [PCWorld.holds_neg, PCWorld.holds_atom] at this
    exact this (hvb.mpr rfl)

omit [∀ Γ φ, Decidable (AxEntails S Γ φ)] in
/-- **4e, `halving_of_fresh_instances`**: fresh instances give the halving condition
(`fresh_undecided` at every level `k n`). This is why the halving witness is not a fluke.
Source: none: this run's theorem (the reason `HalvingCondition` is inhabited by a syntactic
hypothesis)
Kind: P
Fidelity: n/a
Hyps: (a) `FreshInstances` -/
theorem halving_of_fresh_instances (B u : ℕ) (h : FreshInstances S e B u) :
    HalvingCondition S e B u := by
  obtain ⟨k, hk, hkB, hlev, hinst, hfresh⟩ := h
  exact ⟨k, id, hk, hkB, hlev, hinst, fun n w hc hnU =>
    fresh_undecided S e u (k n) n (hlev.trans (hk.monotone (Nat.zero_le n))) (hfresh n) w hc hnU⟩

end Gaifman

/-! ## 4c(i) — the first-counterexample events -/

/-- **4c(i), `tendsto_first_counterexample`**: for *any* finite measure `μ` on `BoolPCWorld` and
any sequence of sentences `φ`, the measures of the "first counterexample at `m`" events
`(⋂ i < m, {φ i}) ∩ {φ m}ᶜ` tend to `0`: the events are pairwise disjoint, so their measures form
a convergent series. PDF 06 footnote 1 states this under `μ(∀mφ) > 0`; the hypothesis is idle —
the content is finite additivity plus boundedness (the events are exclusive, so every finite
partial sum of their measures is `≤ μ univ`, which already forces the terms to `0`), a property of
every finitely additive content on worlds, PDF 06's chained content included, not of the
extrapolation (finding F-3). The proof below uses `measure_iUnion` (σ-additivity) only because
that is the tool a `Measure` offers.
Source: PDF 06 p. 2 footnote 1; [[bli-soto-a-inventory]] 052 (iv)
Kind: P
Fidelity: stronger: no hypothesis on `μ(∀mφ)`; any finite measure
Hyps: (a) none -/
theorem tendsto_first_counterexample (μ : Measure BoolPCWorld) [IsFiniteMeasure μ]
    (φ : ℕ → Sentence) :
    Tendsto (fun m => μ ((⋂ i < m, {v : BoolPCWorld | v.toPCWorld.Holds (φ i)}) ∩
      {v | v.toPCWorld.Holds (φ m)}ᶜ)) atTop (𝓝 0) := by
  set F : ℕ → Set BoolPCWorld := fun m =>
    (⋂ i < m, {v : BoolPCWorld | v.toPCWorld.Holds (φ i)}) ∩ {v | v.toPCWorld.Holds (φ m)}ᶜ
    with hF
  have hmeas : ∀ m, MeasurableSet (F m) := fun m =>
    (MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ => measurableSet_holds _).inter
      (measurableSet_holds _).compl
  have hdisj : Pairwise (Disjoint on F) := by
    have key : ∀ m m', m < m' → Disjoint (F m) (F m') := by
      intro m m' hmm'
      rw [Set.disjoint_left]
      rintro v ⟨_, hvm⟩ ⟨hvm', _⟩
      exact hvm (Set.mem_iInter₂.mp hvm' m hmm')
    intro m m' hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact key m m' h
    · exact (key m' m h).symm
  apply ENNReal.tendsto_atTop_zero_of_tsum_ne_top
  rw [← measure_iUnion hdisj hmeas]
  exact measure_ne_top _ _

end Cleanroom.Bli.BliExtrapolation
