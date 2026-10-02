import Cleanroom.Bli.BliCoherentMm.AttemptB.Accept

/-!
# `bli-coherent-mm` (attempt B) · Interior: the interior, truth-respecting maker (T3, M2)

The accepted region `{p ∈ Δ(W_D) | ∀ u ∈ W_D, value_u(p) < ε}` is open and contains the fixed
point `p*` (T1 at `0`), so it contains the mixture `(1 − t) p* + t · unif(W_D)` for small
`t > 0`, which has every coordinate `≥ t / |W_D|`; rounding that mixture at a mesh `d` with
`1/d < t / |W_D|` keeps every coordinate positive (angle B: `gridRound_ge`). One search parameter
`N` drives both: `t_N := 1/(N+1)`, `d_N := (N+1)²`.

* `mixUnif`, `interiorCandidate`, `InteriorAccepted`, `exists_interiorAccepted` (T3's existence,
  `exists_coherentAccepts_fullSupport` in the mandate's shape), `interiorMesh` (`Nat.find`),
  `interiorWeights`, **`interiorCoherentMarketMaker`** (D4, interior variant) with
  `interior_accepts`, `interior_isWorldMeasure`, `interior_fullSupport`, `interior_coherent`,
  `interior_coherentOn`, `interior_quote_eq_pi`.
* Consequences: **`interior_nonDogmatic`** (an undecided sentence of `S` is priced strictly inside
  `(0,1)`), `interior_decided_at_truth` (T2(c) again), `interior_trichotomy` and
  **`interior_D_ND_day`** (bli-found's `D_ND` clause at day `n`, in the `PCWorld` form, for
  `bli-superbelief`'s E6/L5 customers).

"Full support" means full support **on `W_D B`** — decided sentences stay at `0/1`; the
statement of record is `interior_fullSupport`, the coherent analogue of E5's face condition.

Sources: [[bli-coherent-mm-mandate]] T3, D4; [[bli-program]] §3.8 ("mix in `ε_n` times the
uniform measure"), §2.6 (`D_ND`).
-/

namespace Cleanroom.Bli.BliCoherentMm.AttemptB

open LogicalInduction LogicalInduction.BoolPCWorld LO.Propositional Cleanroom.Bli.BliFound
  Cleanroom.Bli.BliOverlay Cleanroom.Bli.BliFinite Finset

noncomputable section

/-! ## Full-support measures price satisfiable sentences positively (shared with T5) -/

/-- A world measure with full support on `W_D` prices a sentence some `D`-consistent world
holds strictly positively.
Source: [[bli-coherent-mm-mandate]] T3, T5
Kind: L
Fidelity: exact -/
lemma piTable_pos_of_exists_holds {D : Finset Sentence} {B : ℕ} {w : FiniteWorld B → ℚ}
    (hw : IsWorldMeasure D B w) (hfull : ∀ u ∈ worldsOf D B, 0 < w u) {φ : Sentence}
    (h : ∃ u ∈ worldsOf D B, (worldOf u).Holds φ) : 0 < piTable w φ := by
  obtain ⟨u, hu, hφ⟩ := h
  unfold piTable
  calc (0 : ℚ) < w u * u.payoutRat φ := by
        rw [payoutRat_of_holds hφ, mul_one]; exact hfull u hu
    _ ≤ ∑ v, w v * v.payoutRat φ :=
        single_le_sum (fun v _ => mul_nonneg (hw.1 v) (payoutRat_nonneg v φ)) (mem_univ u)

/-- A world measure with full support on `W_D` prices a sentence some `D`-consistent world
fails strictly below one.
Source: [[bli-coherent-mm-mandate]] T3, T5
Kind: L
Fidelity: exact -/
lemma piTable_lt_one_of_exists_not_holds {D : Finset Sentence} {B : ℕ} {w : FiniteWorld B → ℚ}
    (hw : IsWorldMeasure D B w) (hfull : ∀ u ∈ worldsOf D B, 0 < w u) {φ : Sentence}
    (h : ∃ u ∈ worldsOf D B, ¬ (worldOf u).Holds φ) : piTable w φ < 1 := by
  obtain ⟨u, hu, hφ⟩ := h
  unfold piTable
  rw [← hw.2.1]
  apply sum_lt_sum
  · intro v _
    exact mul_le_of_le_one_right (hw.1 v) (payoutRat_le_one v φ)
  · exact ⟨u, mem_univ u, by rw [payoutRat_of_not_holds hφ, mul_zero]; exact hfull u hu⟩

/-! ## Mixing with the uniform distribution -/

section Mix

variable {ι : Type} [Fintype ι]

/-- The mixture `(1 − t) q + t · unif`.
Source: [[bli-program]] §3.8; [[bli-coherent-mm-mandate]] T3
Kind: D
Fidelity: exact -/
def mixUnif (t : ℝ) (q : ι → ℝ) : ι → ℝ :=
  fun u => (1 - t) * q u + t / Fintype.card ι

/-- The mixture of a simplex point with the uniform distribution is a simplex point.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mixUnif_mem [Nonempty ι] {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {q : ι → ℝ}
    (hq : q ∈ stdSimplex ℝ ι) : mixUnif t q ∈ stdSimplex ℝ ι := by
  have hc : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  refine ⟨fun u => add_nonneg (mul_nonneg (by linarith) (hq.1 u)) (div_nonneg ht0 hc.le), ?_⟩
  simp only [mixUnif]
  rw [sum_add_distrib, ← mul_sum, hq.2, sum_const, card_univ, nsmul_eq_mul]
  field_simp
  ring

/-- Every coordinate of the mixture is at least `t / card ι`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mixUnif_ge {t : ℝ} (ht1 : t ≤ 1) {q : ι → ℝ} (hq : q ∈ stdSimplex ℝ ι) (u : ι) :
    t / Fintype.card ι ≤ mixUnif t q u := by
  unfold mixUnif
  have := mul_nonneg (sub_nonneg.mpr ht1) (hq.1 u)
  linarith

/-- The mixture moves every coordinate by at most `t`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma abs_mixUnif_sub_le [Nonempty ι] {t : ℝ} (ht0 : 0 ≤ t) {q : ι → ℝ}
    (hq : q ∈ stdSimplex ℝ ι) (u : ι) : |mixUnif t q u - q u| ≤ t := by
  unfold mixUnif
  have h0 : 0 ≤ q u := hq.1 u
  have h1 : q u ≤ 1 := (mem_Icc_of_mem_stdSimplex hq u).2
  have hc : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hd0 : 0 ≤ t / Fintype.card ι := div_nonneg ht0 (by linarith)
  have hd1 : t / Fintype.card ι ≤ t := div_le_self ht0 hc
  have htq0 : 0 ≤ t * q u := mul_nonneg ht0 h0
  have htq1 : t * q u ≤ t := mul_le_of_le_one_right ht0 h1
  rw [abs_le]
  constructor <;> linarith

end Mix

/-! ## The interior search -/

/-- The mixing weight `1/(N+1)` lies in `(0, 1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mixWeight_mem (N : ℕ) : 0 < 1 / ((N : ℝ) + 1) ∧ 1 / ((N : ℝ) + 1) ≤ 1 := by
  constructor
  · positivity
  · rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]

/-- Every `D`-consistent finite world holds `φ` iff every `D`-consistent `PCWorld` does, within
the atom bound (restriction one way, `worldOf` the other).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma forall_worldsOf_holds_iff {D : Finset Sentence} {B : ℕ} {φ : Sentence}
    (hBD : ∀ ψ ∈ D, atomBound ψ ≤ B) (hφ : atomBound φ ≤ B) :
    (∀ u ∈ worldsOf D B, (worldOf u).Holds φ) ↔
      ∀ v : PCWorld, v.ConsistentWith D → v.Holds φ := by
  constructor
  · intro h v hv
    have := h _ (restrict_mem_worldsOf hBD hv)
    rwa [holds_worldOf_restrict v hφ] at this
  · intro h u hu
    exact h _ (mem_worldsOf.mp hu)

/-- The dual: every `D`-consistent finite world fails `φ` iff every `D`-consistent `PCWorld`
does, within the atom bound.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma forall_worldsOf_not_holds_iff {D : Finset Sentence} {B : ℕ} {φ : Sentence}
    (hBD : ∀ ψ ∈ D, atomBound ψ ≤ B) (hφ : atomBound φ ≤ B) :
    (∀ u ∈ worldsOf D B, ¬ (worldOf u).Holds φ) ↔
      ∀ v : PCWorld, v.ConsistentWith D → ¬ v.Holds φ := by
  constructor
  · intro h v hv
    have := h _ (restrict_mem_worldsOf hBD hv)
    rwa [holds_worldOf_restrict v hφ] at this
  · intro h u hu
    exact h _ (mem_worldsOf.mp hu)

section Interior

variable {n : ℕ} (T : Strategy n) (past : List RationalBeliefState) (D : Finset Sentence) (B : ℕ)
  (hB : ∀ φ ∈ mentionedSet T ∪ D, atomBound φ ≤ B)
  (hW : ∃ u : FiniteWorld B, (worldOf u).ConsistentWith D)

include hB hW

/-- **The interior candidate at parameter `N`**: the fixed point mixed with the uniform
distribution at weight `1/(N+1)`, rounded at mesh `(N+1)²`, extended by zero.
Source: [[bli-coherent-mm-mandate]] T3 (angle B)
Kind: D
Fidelity: exact -/
def interiorCandidate (N : ℕ) : FiniteWorld B → ℚ :=
  extWeightsQ D B (gridRound (anchor D B hW) ((N + 1) ^ 2)
    (mixUnif (1 / ((N : ℝ) + 1)) (fixedPointSub T past D B hB hW)))

/-- **The interior search predicate**: the candidate is a world measure, has full support on
`W_D B`, and is coherently accepted at `ε` on `S`.
Source: [[bli-coherent-mm-mandate]] T3, D4
Kind: D
Fidelity: exact -/
def InteriorAccepted (S : Finset Sentence) (ε : ℚ) (N : ℕ) : Prop :=
  IsWorldMeasure D B (interiorCandidate T past D B hB hW N) ∧
    (∀ u ∈ worldsOf D B, 0 < interiorCandidate T past D B hB hW N u) ∧
    CoherentAccepts T past D B S ε (interiorCandidate T past D B hB hW N)

/-- The interior search predicate is decidable.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
instance instDecidableInteriorAccepted (S : Finset Sentence) (ε : ℚ) :
    DecidablePred (InteriorAccepted T past D B hB hW S ε) := fun _ => by
  unfold InteriorAccepted; infer_instance

/-- The interior candidate is a world measure at every parameter.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma interiorCandidate_isWorldMeasure (N : ℕ) :
    IsWorldMeasure D B (interiorCandidate T past D B hB hW N) := by
  haveI : Nonempty ↥(worldsOf D B) := ⟨anchor D B hW⟩
  have hmem := mixUnif_mem (mixWeight_mem N).1.le (mixWeight_mem N).2
    (fixedPointSub_mem T past D B hB hW)
  have hd : 0 < (N + 1) ^ 2 := by positivity
  refine ⟨fun u => ?_, ?_, fun u hu => extWeightsQ_support D B _ u hu⟩
  · unfold interiorCandidate extWeightsQ
    split_ifs
    · exact gridRound_nonneg _ _ _ _
    · exact le_rfl
  · unfold interiorCandidate
    rw [sum_extWeightsQ]
    exact gridRound_sum _ hd _ hmem.1 hmem.2

/-- **T3 (search form). Some interior parameter is accepted**: for every `ε > 0` and
`S ⊇ mentionedSet T` there is `N` whose interior candidate is a world measure with full support
on `W_D B`, coherently accepted at `ε`.
Source: [[bli-coherent-mm-mandate]] T3
Kind: P
Fidelity: exact
Hyps: (a) `hS`, `hε`, `hB`, `hW` -/
theorem exists_interiorAccepted (S : Finset Sentence) (hS : mentionedSet T ⊆ S) {ε : ℚ}
    (hε : 0 < ε) : ∃ N, InteriorAccepted T past D B hB hW S ε N := by
  haveI : Nonempty ↥(worldsOf D B) := ⟨anchor D B hW⟩
  have hεr : (0 : ℝ) < ε := by exact_mod_cast hε
  have hle : ∀ u : ↥(worldsOf D B),
      worldValue T past (extWeights D B (fixedPointSub T past D B hB hW)) u.1 ≤ 0 := by
    rw [extWeights_fixedPointSub]
    exact fun u => (fixedPointWeights_spec T past D B hB hW).2 u.1 u.2
  obtain ⟨δ, hδ, hδspec⟩ := exists_delta_of_fixed T past D B _ hle hεr
  set c : ℝ := ((Fintype.card ↥(worldsOf D B) : ℕ) : ℝ) with hc
  have hc1 : 1 ≤ c := by rw [hc]; exact_mod_cast Fintype.card_pos
  obtain ⟨N, hN⟩ := exists_nat_gt (max (2 / δ) (c + 1))
  have hN1 : (0 : ℝ) < N + 1 := by positivity
  have hNδ : 2 / δ < (N : ℝ) + 1 := lt_trans (lt_of_le_of_lt (le_max_left _ _) hN) (by linarith)
  have hNc : c + 1 < (N : ℝ) + 1 := lt_trans (lt_of_le_of_lt (le_max_right _ _) hN) (by linarith)
  set t : ℝ := 1 / ((N : ℝ) + 1) with ht
  have ht0 : 0 < t := (mixWeight_mem N).1
  have ht1 : t ≤ 1 := (mixWeight_mem N).2
  have htδ : t < δ / 2 := by
    rw [ht, div_lt_iff₀ hN1]
    rw [div_lt_iff₀ hδ] at hNδ
    linarith
  have hd : 0 < (N + 1) ^ 2 := by positivity
  have hdr : ((((N + 1) ^ 2 : ℕ)) : ℝ) = ((N : ℝ) + 1) ^ 2 := by push_cast; ring
  have hdpos : (0 : ℝ) < (((N + 1) ^ 2 : ℕ) : ℝ) := by rw [hdr]; positivity
  -- the rounding error `c / d` is below `t`, hence below `δ / 2`
  have hround : c / (((N + 1) ^ 2 : ℕ) : ℝ) < t := by
    rw [hdr, ht, div_lt_div_iff₀ (by positivity) hN1]
    nlinarith
  have hone : (1 : ℝ) / (((N + 1) ^ 2 : ℕ) : ℝ) ≤ c / (((N + 1) ^ 2 : ℕ) : ℝ) :=
    div_le_div_of_nonneg_right hc1 hdpos.le
  have hmem := mixUnif_mem ht0.le ht1 (fixedPointSub_mem T past D B hB hW)
  refine ⟨N, interiorCandidate_isWorldMeasure T past D B hB hW N, ?_, ?_⟩
  · -- full support: every rounded coordinate is at least `t / c − 1 / d > 0`
    intro u hu
    unfold interiorCandidate
    rw [extWeightsQ_of_mem D B _ hu]
    have hge := gridRound_ge (anchor D B hW) hd (mixUnif t (fixedPointSub T past D B hB hW)) ⟨u, hu⟩
    have hmix := mixUnif_ge ht1 (fixedPointSub_mem T past D B hB hW) ⟨u, hu⟩
    have hkey : (1 : ℝ) / (((N + 1) ^ 2 : ℕ) : ℝ) < t / c := by
      rw [hdr, ht, div_div, div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have hpos : (0 : ℝ) < (gridRound (anchor D B hW) ((N + 1) ^ 2)
        (mixUnif t (fixedPointSub T past D B hB hW)) ⟨u, hu⟩ : ℝ) := by
      rw [hc] at hkey
      linarith
    exact Rat.cast_pos.mp hpos
  · apply coherentAccepts_of_real T past (interiorCandidate_isWorldMeasure T past D B hB hW N) hS
    intro u hu
    unfold interiorCandidate
    rw [cast_extWeightsQ]
    refine (hδspec _ (fun v => ?_) ⟨u, hu⟩).le
    have h1 := gridRound_ge (anchor D B hW) hd (mixUnif t (fixedPointSub T past D B hB hW)) v
    have h2 := gridRound_le (anchor D B hW) hd (mixUnif t (fixedPointSub T past D B hB hW))
      hmem.1 hmem.2 v
    have h3 := abs_mixUnif_sub_le ht0.le (fixedPointSub_mem T past D B hB hW) v
    rw [abs_le] at h3
    rw [abs_sub_lt_iff]
    rw [← hc] at h2
    constructor <;> linarith

/-- **T3. Full-support coherent acceptance is satisfiable** (the mandate's statement shape):
for every `ε > 0` there is a world measure with full support on `W_D B` accepted at `ε`.
Source: [[bli-coherent-mm-mandate]] T3 (`exists_coherentAccepts_fullSupport`)
Kind: P
Fidelity: exact (acceptance at the same `ε`; the mixing weight is chosen inside the proof)
Hyps: (a) `hS`, `hε`, `hB`, `hW` -/
theorem exists_coherentAccepts_fullSupport (S : Finset Sentence) (hS : mentionedSet T ⊆ S)
    {ε : ℚ} (hε : 0 < ε) :
    ∃ w : FiniteWorld B → ℚ, IsWorldMeasure D B w ∧ (∀ u ∈ worldsOf D B, 0 < w u) ∧
      CoherentAccepts T past D B S ε w := by
  obtain ⟨N, hmeas, hfull, hacc⟩ := exists_interiorAccepted T past D B hB hW S hS hε
  exact ⟨_, hmeas, hfull, hacc⟩

/-- **D4. The accepted interior parameter** (`Nat.find`).
Source: [[bli-coherent-mm-mandate]] D4 (interior variant)
Kind: D
Fidelity: exact -/
def interiorMesh (S : Finset Sentence) (hS : mentionedSet T ⊆ S) (ε : ℚ) (hε : 0 < ε) : ℕ :=
  Nat.find (exists_interiorAccepted T past D B hB hW S hS hε)

/-- **D4 (definition of record). The interior coherent weights**: the day-`n` world measure with
full support on `W_D B`.
Source: [[bli-coherent-mm-mandate]] D4 (`coherentWeights`, interior variant)
Kind: D
Fidelity: exact -/
def interiorWeights (S : Finset Sentence) (hS : mentionedSet T ⊆ S) (ε : ℚ) (hε : 0 < ε) :
    FiniteWorld B → ℚ :=
  interiorCandidate T past D B hB hW (interiorMesh T past D B hB hW S hS ε hε)

/-- **D4 (definition of record). The interior coherent market maker**: the candidate state of
the interior weights on `S` — non-dogmatic on every sentence of `S` undecided by `D`, pricing
decided sentences at their truth.
Source: [[bli-coherent-mm-mandate]] D4 (`interiorCoherentMarketMaker`); [[bli-program]] §3.8
Kind: D
Fidelity: exact -/
def interiorCoherentMarketMaker (S : Finset Sentence) (hS : mentionedSet T ⊆ S) (ε : ℚ)
    (hε : 0 < ε) : RationalBeliefState :=
  ofWeights S (interiorWeights T past D B hB hW S hS ε hε)

variable (S : Finset Sentence) (hS : mentionedSet T ⊆ S) (ε : ℚ) (hε : 0 < ε)

/-- The accepted interior parameter is accepted.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma interiorMesh_spec :
    InteriorAccepted T past D B hB hW S ε (interiorMesh T past D B hB hW S hS ε hε) :=
  Nat.find_spec (exists_interiorAccepted T past D B hB hW S hS hε)

/-- **T3. The interior weights are a world measure.**
Source: [[bli-coherent-mm-mandate]] T3 (`interior_coherent`)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem interior_isWorldMeasure : IsWorldMeasure D B (interiorWeights T past D B hB hW S hS ε hε) :=
  (interiorMesh_spec T past D B hB hW S hS ε hε).1

/-- **T3. Full support on `W_D B`**: every `D`-consistent world has positive weight.
Source: [[bli-coherent-mm-mandate]] T3 (`interior_fullSupport`)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem interior_fullSupport : ∀ u ∈ worldsOf D B, 0 < interiorWeights T past D B hB hW S hS ε hε u :=
  (interiorMesh_spec T past D B hB hW S hS ε hε).2.1

/-- **T3. The interior maker is coherently accepted** at `ε` in every `D`-consistent world.
Source: [[bli-coherent-mm-mandate]] T3 (`interior_accepts`)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem interior_accepts :
    CoherentAccepts T past D B S ε (interiorWeights T past D B hB hW S hS ε hε) :=
  (interiorMesh_spec T past D B hB hW S hS ε hε).2.2

/-- The interior maker's quote is the marginal of its weights on `S`.
Source: [[bli-coherent-mm-mandate]] D4
Kind: L
Fidelity: exact -/
theorem interior_quote_eq_pi {φ : Sentence} (hφ : φ ∈ S) :
    (interiorCoherentMarketMaker T past D B hB hW S hS ε hε).quote φ =
      piTable (interiorWeights T past D B hB hW S hS ε hε) φ :=
  ofWeights_quote_of_mem (interior_isWorldMeasure T past D B hB hW S hS ε hε) hφ

/-- **T3. The interior maker's table is a world marginal on `S`** (extended-table form, as
`coherentMarketMaker_coherent`).
Source: [[bli-coherent-mm-mandate]] T3 (`interior_coherent`)
Kind: C
Fidelity: variant: `IsWorldMarginal` of the extended table, plus quote = table on `S`
Hyps: (a) -/
theorem interior_coherent :
    IsWorldMarginal (piTable (interiorWeights T past D B hB hW S hS ε hε)) S D B ∧
      ∀ φ ∈ S, (interiorCoherentMarketMaker T past D B hB hW S hS ε hε).quote φ =
        piTable (interiorWeights T past D B hB hW S hS ε hε) φ :=
  ⟨piTable_isWorldMarginal (interior_isWorldMeasure T past D B hB hW S hS ε hε) S,
    fun _ hφ => interior_quote_eq_pi T past D B hB hW S hS ε hε hφ⟩

/-- **T3, `CoherentOn` form.**
Source: [[bli-coherent-mm-mandate]] T3
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem interior_coherentOn :
    CoherentOn (𝒮 := constIndex S) (m := n)
      (fun φ => (interiorCoherentMarketMaker T past D B hB hW S hS ε hε).quote φ.1) D B := by
  have hw := interior_isWorldMeasure T past D B hB hW S hS ε hε
  exact ⟨_, hw.1, hw.2.1, hw.2.2, fun φ => interior_quote_eq_pi T past D B hB hW S hS ε hε φ.2⟩

/-- **T3. Non-dogmatism.** A sentence of `S` that some `D`-consistent finite world holds and
some `D`-consistent finite world fails is priced strictly inside `(0, 1)`.
Source: [[bli-coherent-mm-mandate]] T3 (`interior_nonDogmatic`); [[bli-program]] §2.6, §3.8
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem interior_nonDogmatic {φ : Sentence} (hφ : φ ∈ S)
    (h1 : ∃ u ∈ worldsOf D B, (worldOf u).Holds φ)
    (h0 : ∃ u ∈ worldsOf D B, ¬ (worldOf u).Holds φ) :
    0 < (interiorCoherentMarketMaker T past D B hB hW S hS ε hε).quote φ ∧
      (interiorCoherentMarketMaker T past D B hB hW S hS ε hε).quote φ < 1 := by
  rw [interior_quote_eq_pi T past D B hB hW S hS ε hε hφ]
  have hw := interior_isWorldMeasure T past D B hB hW S hS ε hε
  have hfull := interior_fullSupport T past D B hB hW S hS ε hε
  exact ⟨piTable_pos_of_exists_holds hw hfull h1, piTable_lt_one_of_exists_not_holds hw hfull h0⟩

/-- **T3. Decided sentences are priced at their truth** (T2(c) for the interior maker).
Source: [[bli-coherent-mm-mandate]] T3 (`interior_decided_at_truth`)
Kind: L
Fidelity: exact -/
theorem interior_decided_at_truth {φ : Sentence} (hφ : φ ∈ S) :
    ((∀ v : PCWorld, v.ConsistentWith D → v.Holds φ) →
      (interiorCoherentMarketMaker T past D B hB hW S hS ε hε).quote φ = 1) ∧
    ((∀ v : PCWorld, v.ConsistentWith D → ¬ v.Holds φ) →
      (interiorCoherentMarketMaker T past D B hB hW S hS ε hε).quote φ = 0) := by
  rw [interior_quote_eq_pi T past D B hB hW S hS ε hε hφ]
  have hw := interior_isWorldMeasure T past D B hB hW S hS ε hε
  exact ⟨piTable_eq_one_of_decided hw, piTable_eq_zero_of_decided_false hw⟩

/-- **T3, the `D_ND` clause at day `n`** (bli-found's `D_ND`, `PCWorld` form, for one day and
the sentence set `S`): every `φ ∈ S` within the atom bound is decided true by `D`, decided
false by `D`, or priced strictly inside `(0, 1)` by the interior maker. With `S = smallSet n`
this is literally `D_ND`'s day-`n` clause (cast to `ℝ` by the customer).
Source: [[bli-coherent-mm-mandate]] T3 (`interior_D_ND_day`); [[bli-program]] §2.6 (`D_ND`)
Kind: C
Fidelity: exact (one day; the `ℝ`-cast of the quote is the customer's `Q n φ`)
Hyps: (a) `hBS` (the atom bound covers `S`; it already covers `D` by `hB`) -/
theorem interior_D_ND_day (hBS : ∀ φ ∈ S, atomBound φ ≤ B) :
    ∀ φ ∈ S, (∀ v : PCWorld, v.ConsistentWith D → v.Holds φ) ∨
      (∀ v : PCWorld, v.ConsistentWith D → ¬ v.Holds φ) ∨
      (0 < (interiorCoherentMarketMaker T past D B hB hW S hS ε hε).quote φ ∧
        (interiorCoherentMarketMaker T past D B hB hW S hS ε hε).quote φ < 1) := by
  intro φ hφ
  have hBD : ∀ ψ ∈ D, atomBound ψ ≤ B := fun ψ hψ => hB ψ (Finset.mem_union_right _ hψ)
  by_cases h1 : ∀ u ∈ worldsOf D B, (worldOf u).Holds φ
  · exact Or.inl ((forall_worldsOf_holds_iff hBD (hBS φ hφ)).mp h1)
  by_cases h0 : ∀ u ∈ worldsOf D B, ¬ (worldOf u).Holds φ
  · exact Or.inr (Or.inl ((forall_worldsOf_not_holds_iff hBD (hBS φ hφ)).mp h0))
  refine Or.inr (Or.inr (interior_nonDogmatic T past D B hB hW S hS ε hε hφ ?_ ?_))
  · simp only [not_forall, exists_prop] at h0
    obtain ⟨u, hu, hu'⟩ := h0
    exact ⟨u, hu, not_not.mp hu'⟩
  · simp only [not_forall, exists_prop] at h1
    exact h1

end Interior

end

end Cleanroom.Bli.BliCoherentMm.AttemptB
