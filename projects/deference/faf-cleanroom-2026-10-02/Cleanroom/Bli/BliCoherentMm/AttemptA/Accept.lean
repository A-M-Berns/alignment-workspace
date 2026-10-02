import Cleanroom.Bli.BliCoherentMm.AttemptA.FixedPoint

/-!
# `bli-coherent-mm` (attempt A) · Accept: coherent acceptance (D3), existence (T2(a), T3(a)), the entry point (T2(d))

* **D3** `CoherentAccepts T past D B S ε w`: `w` is a world measure over `D` and the exact
  rational value of `T` on the candidate table (`π w` on `S`, `0` off `S`, the past on days
  `< n`) is `≤ ε` in **every `D`-consistent world over `B` atoms** — never over all Boolean
  tables on the support (`Contrast.lean` shows that predicate is unsatisfiable by coherent
  prices). Decidable (`instDecidableCoherentAccepts`): finite worlds, exact rational arithmetic.
* **T2(a)** `exists_coherentAccepts`: a rational accepted measure exists for every `ε > 0`, from
  T1 by continuity and the density of rational simplex points (`exists_rat_simplex_near`, proved
  here: coordinatewise rational rounding *down* with the deficit returned to one coordinate).
* **T3(a)** `exists_coherentAccepts_fullSupport`: and one with full support on `WD D B` — mix
  `t · uniform` into the fixed point, then round keeping every coordinate positive.
* **T2(d)** `dayValue_le_of_coherentAccepts`: the customer's entry point — on any real history
  agreeing with the candidate table on the cells `T` mentions, `T`'s value is `≤ ε` in every
  `PCWorld` consistent with `D` (the coherent twin of `bli-overlay`'s
  `dayValue_le_of_accepted_state`, whose all-Boolean hypothesis a coherent table cannot meet).

Sources: [[bli-coherent-mm-mandate]] D3, T2(a), T2(d), T3; [[bli-program]] §3.8.
-/

namespace Cleanroom.Bli.BliCoherentMm.AttemptA

open LogicalInduction LO.Propositional BoolPCWorld Cleanroom.Bli.BliFound Cleanroom.Bli.BliFinite
  Cleanroom.Bli.BliOverlay

/-! ## Rational points are dense in the simplex -/

/-- **Rational simplex points approximate real ones, preserving positivity.** For `p` in the
simplex and `δ > 0` there is a rational probability vector `q` within `δ` of `p` in every
coordinate, positive wherever `p` is. Proof: round every coordinate but `x₀` down to a rational
in `(max (p x − δ/N) (p x / 2), p x)` (or `0` where `p x = 0`), and give `x₀` the remaining mass,
which exceeds `p x₀` by less than `(N−1)·δ/N < δ`.
Source: [[bli-coherent-mm-mandate]] T2(a) ("density of rational points in the simplex"); FAF's
`exists_rationalPriceVector_good` is the cube version
Kind: P
Fidelity: n/a -/
lemma exists_rat_simplex_near {ι : Type} [Fintype ι] [Nonempty ι] (p : ι → ℝ)
    (hp : p ∈ stdSimplex ℝ ι) {δ : ℝ} (hδ : 0 < δ) :
    ∃ q : ι → ℚ, (∀ x, 0 ≤ q x) ∧ ∑ x, q x = 1 ∧ (∀ x, 0 < p x → 0 < q x) ∧
      ∀ x, |(q x : ℝ) - p x| < δ := by
  classical
  obtain ⟨x₀⟩ := ‹Nonempty ι›
  set N : ℝ := (Fintype.card ι : ℝ) with hN
  have hNpos : 0 < N := by rw [hN]; exact_mod_cast Fintype.card_pos
  have hN1 : 1 ≤ N := by rw [hN]; exact_mod_cast Fintype.card_pos
  have hη : 0 < δ / N := div_pos hδ hNpos
  have hηδ : δ / N ≤ δ := div_le_self hδ.le hN1
  have hchoice : ∀ x, ∃ r : ℚ, 0 ≤ r ∧ (r : ℝ) ≤ p x ∧ (0 < p x → 0 < r) ∧
      p x - (r : ℝ) < δ / N := by
    intro x
    rcases (hp.1 x).lt_or_eq with hpx | hpx
    · have hlt : max (p x - δ / N) (p x / 2) < p x := max_lt (by linarith) (by linarith)
      obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hlt
      have hr0 : (0 : ℝ) < r :=
        lt_of_le_of_lt (le_trans (half_pos hpx).le (le_max_right _ _)) hr1
      refine ⟨r, by exact_mod_cast hr0.le, hr2.le, fun _ => by exact_mod_cast hr0, ?_⟩
      have := le_max_left (p x - δ / N) (p x / 2)
      linarith
    · refine ⟨0, le_rfl, by rw [← hpx]; simp, fun h => absurd h (by rw [← hpx]; exact lt_irrefl 0),
        ?_⟩
      rw [← hpx]
      simpa using hη
  choose r hr0 hrle hrpos hrnear using hchoice
  let q : ι → ℚ := fun x => if x = x₀ then 1 - ∑ y ∈ Finset.univ.erase x₀, r y else r x
  have hq_ne : ∀ x, x ≠ x₀ → q x = r x := fun x hx => by simp [q, hx]
  have hq0 : (q x₀ : ℝ) = 1 - ∑ y ∈ Finset.univ.erase x₀, (r y : ℝ) := by
    simp only [q, if_pos rfl]
    push_cast
    rfl
  have hsum_p : ∑ y ∈ Finset.univ.erase x₀, p y = 1 - p x₀ := by
    have h := Finset.sum_erase_add Finset.univ p (Finset.mem_univ x₀)
    rw [hp.2] at h
    linarith
  have hsum_le : ∑ y ∈ Finset.univ.erase x₀, (r y : ℝ) ≤ ∑ y ∈ Finset.univ.erase x₀, p y :=
    Finset.sum_le_sum fun y _ => hrle y
  have hq0_ge : p x₀ ≤ (q x₀ : ℝ) := by rw [hq0]; linarith
  have hq0_lt : (q x₀ : ℝ) - p x₀ < δ := by
    rw [hq0]
    have hcard : ((Finset.univ.erase x₀).card : ℝ) < N := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ x₀), Finset.card_univ, hN]
      exact_mod_cast Nat.sub_lt Fintype.card_pos one_pos
    have h1 : ∑ y ∈ Finset.univ.erase x₀, (p y - (r y : ℝ)) ≤
        ∑ _y ∈ Finset.univ.erase x₀, δ / N :=
      Finset.sum_le_sum fun y _ => (hrnear y).le
    rw [Finset.sum_const, nsmul_eq_mul, Finset.sum_sub_distrib] at h1
    have h2 : ((Finset.univ.erase x₀).card : ℝ) * (δ / N) < δ := by
      calc ((Finset.univ.erase x₀).card : ℝ) * (δ / N) < N * (δ / N) :=
            mul_lt_mul_of_pos_right hcard hη
        _ = δ := by field_simp
    linarith
  refine ⟨q, ?_, ?_, ?_, ?_⟩
  · intro x
    by_cases hx : x = x₀
    · subst hx
      have h : (0 : ℝ) ≤ q x := le_trans (hp.1 x) hq0_ge
      exact_mod_cast h
    · rw [hq_ne x hx]
      exact hr0 x
  · rw [← Finset.sum_erase_add _ _ (Finset.mem_univ x₀)]
    have h : ∑ y ∈ Finset.univ.erase x₀, q y = ∑ y ∈ Finset.univ.erase x₀, r y :=
      Finset.sum_congr rfl fun y hy => hq_ne y (Finset.ne_of_mem_erase hy)
    rw [h]
    simp [q]
  · intro x hx
    by_cases hxx : x = x₀
    · subst hxx
      have h : (0 : ℝ) < q x := lt_of_lt_of_le hx hq0_ge
      exact_mod_cast h
    · rw [hq_ne x hxx]
      exact hrpos x hx
  · intro x
    by_cases hxx : x = x₀
    · subst hxx
      rw [abs_lt]
      constructor <;> linarith
    · rw [hq_ne x hxx, abs_lt]
      constructor <;> linarith [hrle x, hrnear x, hηδ]

/-! ## Rational extension by zero -/

/-- Extension by zero of a rational vector on the consistent worlds.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def extQ (D : Finset Sentence) (B : ℕ) (q : ↥(WD D B) → ℚ) : FiniteWorld B → ℚ :=
  fun u => if h : u ∈ WD D B then q ⟨u, h⟩ else 0

/-- The cast of the rational extension is the real extension of the cast.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma extQ_cast {D : Finset Sentence} {B : ℕ} (q : ↥(WD D B) → ℚ) :
    (fun u => (extQ D B q u : ℝ)) = extR D B fun x => (q x : ℝ) := by
  funext u
  unfold extQ extR
  split_ifs <;> simp

/-- A rational simplex point on the consistent worlds extends to a world measure.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma isWorldMeasure_extQ {D : Finset Sentence} {B : ℕ} (q : ↥(WD D B) → ℚ) (hq0 : ∀ x, 0 ≤ q x)
    (hq1 : ∑ x, q x = 1) : IsWorldMeasure (extQ D B q) D := by
  refine ⟨fun u => ?_, ?_, fun u hu => ?_⟩
  · unfold extQ
    split_ifs
    · exact hq0 _
    · exact le_rfl
  · have h : ((∑ u, extQ D B q u : ℚ) : ℝ) = 1 := by
      push_cast
      rw [show (fun u => (extQ D B q u : ℝ)) = extR D B (fun x => (q x : ℝ)) from extQ_cast q]
      rw [sum_extR]
      exact_mod_cast hq1
    exact_mod_cast h
  · by_contra hcon
    apply hu
    unfold extQ
    rw [dif_neg (fun h => hcon (mem_WD.mp h))]

/-! ## D3: coherent acceptance -/

/-- **D3. Coherent acceptance.** `w` is a world measure over `D` and the exact rational value of
`T` on the candidate table `candidateTable past n S w` (`π w` on `S`, `0` off `S`, the past on
days `< n`) is at most `ε` in every `D`-consistent world over `B` atoms. **Scope: over
`D`-consistent worlds**, not FAF's `supportBitWorldRat T b` for all `b` — that predicate is
unsatisfiable by coherent prices in general (`Contrast.lean`, T4(a)). Use with
`S ⊇ mentionedSet T` (a hypothesis of the existence theorems: it makes the candidate table the
table `T` reads).
Source: [[bli-coherent-mm-mandate]] D3
Kind: D
Fidelity: exact -/
def CoherentAccepts {n : ℕ} (T : Strategy n) (past : List RationalBeliefState)
    (D : Finset Sentence) (B : ℕ) (S : Finset Sentence) (ε : ℚ) (w : FiniteWorld B → ℚ) : Prop :=
  IsWorldMeasure w D ∧
    ∀ u ∈ WD D B, T.marketValueRat (candidateTable past n S w) u.payoutRat ≤ ε

/-- **The acceptance test is decidable**: a finite scan of `WD D B` with exact rational
arithmetic (FAF's `denoteRat`), plus the decidable `IsWorldMeasure`.
Source: [[bli-coherent-mm-mandate]] D3 ("decidable for the search")
Kind: L
Fidelity: n/a -/
instance instDecidableCoherentAccepts {n : ℕ} (T : Strategy n) (past : List RationalBeliefState)
    (D : Finset Sentence) (B : ℕ) (S : Finset Sentence) (ε : ℚ) (w : FiniteWorld B → ℚ) :
    Decidable (CoherentAccepts T past D B S ε w) := by
  unfold CoherentAccepts
  infer_instance

/-- D3 in the mandate's FAF-facing shape: for a world measure, acceptance is the bound on
`candidateRationalHistory past n (ofWeights S w hw)` in every `D`-consistent world.
Source: [[bli-coherent-mm-mandate]] D3
Kind: L
Fidelity: exact -/
lemma coherentAccepts_iff {n : ℕ} (T : Strategy n) (past : List RationalBeliefState)
    (D : Finset Sentence) (B : ℕ) (S : Finset Sentence) (ε : ℚ) {w : FiniteWorld B → ℚ}
    (hw : IsWorldMeasure w D) :
    CoherentAccepts T past D B S ε w ↔
      ∀ u ∈ WD D B,
        T.marketValueRat (candidateRationalHistory past n (ofWeights S w hw)) u.payoutRat ≤ ε := by
  rw [candidateRationalHistory_ofWeights past n S w hw]
  exact ⟨fun h => h.2, fun h => ⟨hw, h⟩⟩

/-! ## The candidate table and the fixed point's history agree on mentioned cells -/

/-- On the cells `(k ≤ n, φ ∈ S)` the cast candidate table is the fixed point's history of the
cast weights.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma candidateTable_cast_eq_worldHistory (past : List RationalBeliefState) (n : ℕ)
    (S : Finset Sentence) {B : ℕ} (w : FiniteWorld B → ℚ) {φ : Sentence} (hφ : φ ∈ S) {k : ℕ}
    (hk : k ≤ n) :
    (candidateTable past n S w k φ : ℝ) = worldHistory (beliefHistory past) n (fun u => (w u : ℝ)) k φ := by
  rcases Nat.lt_or_eq_of_le hk with hk | rfl
  · rw [candidateTable_of_ne past hk.ne S w, worldHistory_of_ne _ hk.ne]
    rfl
  · rw [candidateTable_self_of_mem past k w hφ, worldHistory_self, worldTable_cast]

/-- The exact rational value on the candidate table, in a finite world, is the real value on the
fixed point's history of the cast weights (`S ⊇ mentionedSet T`).
Source: [[bli-coherent-mm-mandate]] T2(a) (the locality remark)
Kind: L
Fidelity: n/a -/
lemma marketValueRat_candidateTable_cast {n : ℕ} (T : Strategy n) (past : List RationalBeliefState)
    (S : Finset Sentence) (hS : mentionedSet T ⊆ S) {B : ℕ} (w : FiniteWorld B → ℚ)
    (u : FiniteWorld B) :
    (T.marketValueRat (candidateTable past n S w) u.payoutRat : ℝ) =
      T.value (worldHistory (beliefHistory past) n (fun u => (w u : ℝ))) (payoutReal u) := by
  rw [← T.value_eq_marketRatCast (fun k φ => (candidateTable past n S w k φ : ℝ)) _
    (fun _ _ => rfl) (payoutReal u) u.payoutRat (fun _ => rfl)]
  exact Strategy.value_eq_of_eqOn_mentioned T _ _ _ fun φ hφ k hk =>
    candidateTable_cast_eq_worldHistory past n S w (hS (mem_mentionedSet_iff.mpr hφ)) hk

/-! ## T2(a): an accepted rational world measure exists -/

/-- The accepted region in simplex coordinates is open.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma isOpen_acceptedRegion {n : ℕ} (T : Strategy n) (prior : History) (D : Finset Sentence)
    (B : ℕ) (ε : ℝ) :
    IsOpen {p : ↥(WD D B) → ℝ | ∀ x, worldValue T prior D B p x < ε} := by
  have h : {p : ↥(WD D B) → ℝ | ∀ x, worldValue T prior D B p x < ε} =
      ⋂ x, (fun p => worldValue T prior D B p x) ⁻¹' Set.Iio ε := by
    ext p
    simp
  rw [h]
  exact isOpen_iInter_of_finite fun x => isOpen_Iio.preimage (continuous_worldValue T prior D B x)

/-- From a rational simplex point in the accepted region to coherent acceptance.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma coherentAccepts_extQ_of_lt {n : ℕ} (T : Strategy n) (past : List RationalBeliefState)
    (D : Finset Sentence) (B : ℕ) (S : Finset Sentence) (hS : mentionedSet T ⊆ S) (ε : ℚ)
    (q : ↥(WD D B) → ℚ) (hq0 : ∀ x, 0 ≤ q x) (hq1 : ∑ x, q x = 1)
    (hqU : ∀ x, worldValue T (beliefHistory past) D B (fun x => (q x : ℝ)) x < ε) :
    CoherentAccepts T past D B S ε (extQ D B q) := by
  refine ⟨isWorldMeasure_extQ q hq0 hq1, fun u hu => ?_⟩
  have h := hqU ⟨u, hu⟩
  unfold worldValue at h
  rw [← extQ_cast q, ← marketValueRat_candidateTable_cast T past S hS (extQ D B q) u] at h
  exact_mod_cast h.le

/-- **T2(a). An accepted rational world measure exists** for every `ε > 0`: T1's fixed point lies
in the open accepted region `{p | ∀ u ∈ WD D B, value_u (p) < ε}`, which therefore contains a
rational simplex point; its extension by zero is a world measure accepted at `ε`.
Source: [[bli-coherent-mm-mandate]] T2(a); [[bli-program]] §3.8 ("exists by continuity near `p*`")
Kind: P
Fidelity: exact
Hyps: (a) `hS` (the candidate table is the table `T` reads), `hW` (nonempty simplex),
`hε` (the search's tolerance) -/
theorem exists_coherentAccepts {n : ℕ} (T : Strategy n) (past : List RationalBeliefState)
    (D : Finset Sentence) (B : ℕ) (S : Finset Sentence) (hS : mentionedSet T ⊆ S)
    (hW : ∃ u : FiniteWorld B, (worldOf u).ConsistentWith D) {ε : ℚ} (hε : 0 < ε) :
    ∃ w : FiniteWorld B → ℚ, CoherentAccepts T past D B S ε w := by
  haveI : Nonempty ↥(WD D B) := by
    obtain ⟨u, hu⟩ := hW
    exact ⟨⟨u, mem_WD.mpr hu⟩⟩
  obtain ⟨p, hp, hval⟩ := exists_fixedPoint_worldValue T (beliefHistory past) D B hW
  have hpU : p ∈ {p : ↥(WD D B) → ℝ | ∀ x, worldValue T (beliefHistory past) D B p x < ε} :=
    fun x => lt_of_le_of_lt (hval x) (by exact_mod_cast hε)
  obtain ⟨δ, hδ, hball⟩ :=
    Metric.isOpen_iff.mp (isOpen_acceptedRegion T (beliefHistory past) D B ε) p hpU
  obtain ⟨q, hq0, hq1, -, hqnear⟩ := exists_rat_simplex_near p hp hδ
  have hqU : (fun x => (q x : ℝ)) ∈
      {p : ↥(WD D B) → ℝ | ∀ x, worldValue T (beliefHistory past) D B p x < ε} := by
    apply hball
    rw [Metric.mem_ball, dist_pi_lt_iff hδ]
    intro x
    rw [Real.dist_eq]
    exact hqnear x
  exact ⟨extQ D B q, coherentAccepts_extQ_of_lt T past D B S hS ε q hq0 hq1 hqU⟩

/-! ## T3(a): an accepted measure with full support exists -/

/-- **T3(a). An accepted rational world measure with full support on `WD D B` exists** for every
`ε > 0`: mix `t · uniform` into T1's fixed point for a small `t > 0` (still inside the open
accepted region, now with every coordinate positive), then take a rational simplex point nearby
that keeps every coordinate positive (`exists_rat_simplex_near`). Stated at the same `ε` as the
acceptance; the mixing weight is chosen inside the proof.
Source: [[bli-coherent-mm-mandate]] T3; [[bli-program]] §3.8 ("mix in `ε_n` times the uniform measure")
Kind: P
Fidelity: exact
Hyps: (a) `hS`, `hW`, `hε` as in `exists_coherentAccepts` -/
theorem exists_coherentAccepts_fullSupport {n : ℕ} (T : Strategy n)
    (past : List RationalBeliefState) (D : Finset Sentence) (B : ℕ) (S : Finset Sentence)
    (hS : mentionedSet T ⊆ S) (hW : ∃ u : FiniteWorld B, (worldOf u).ConsistentWith D) {ε : ℚ}
    (hε : 0 < ε) :
    ∃ w : FiniteWorld B → ℚ, (∀ u ∈ WD D B, 0 < w u) ∧ CoherentAccepts T past D B S ε w := by
  haveI : Nonempty ↥(WD D B) := by
    obtain ⟨u, hu⟩ := hW
    exact ⟨⟨u, mem_WD.mpr hu⟩⟩
  obtain ⟨p, hp, hval⟩ := exists_fixedPoint_worldValue T (beliefHistory past) D B hW
  have hpU : p ∈ {p : ↥(WD D B) → ℝ | ∀ x, worldValue T (beliefHistory past) D B p x < ε} :=
    fun x => lt_of_le_of_lt (hval x) (by exact_mod_cast hε)
  obtain ⟨δ, hδ, hball⟩ :=
    Metric.isOpen_iff.mp (isOpen_acceptedRegion T (beliefHistory past) D B ε) p hpU
  -- the mixture with the uniform measure
  set t : ℝ := min (δ / 2) 1 with ht
  have ht0 : 0 < t := lt_min (half_pos hδ) one_pos
  have ht1 : t ≤ 1 := min_le_right _ _
  have htδ : t ≤ δ / 2 := min_le_left _ _
  set N : ℝ := (Fintype.card ↥(WD D B) : ℝ) with hN
  have hNpos : 0 < N := by rw [hN]; exact_mod_cast Fintype.card_pos
  have hN1 : 1 ≤ N := by rw [hN]; exact_mod_cast Fintype.card_pos
  let p' : ↥(WD D B) → ℝ := fun x => (1 - t) * p x + t / N
  have hp'pos : ∀ x, 0 < p' x := fun x =>
    add_pos_of_nonneg_of_pos (mul_nonneg (by linarith) (hp.1 x)) (div_pos ht0 hNpos)
  have hp' : p' ∈ stdSimplex ℝ ↥(WD D B) := by
    refine ⟨fun x => (hp'pos x).le, ?_⟩
    simp only [p']
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hp.2, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, ← hN]
    field_simp
    ring
  have hp_le : ∀ x, p x ≤ 1 := fun x => by
    rw [← hp.2]
    exact Finset.single_le_sum (fun y _ => hp.1 y) (Finset.mem_univ x)
  have hp'near : ∀ x, |p' x - p x| ≤ δ / 2 := by
    intro x
    have h : p' x - p x = t * (1 / N - p x) := by simp only [p']; ring
    rw [h, abs_mul, abs_of_pos ht0]
    have h1 : |1 / N - p x| ≤ 1 := by
      rw [abs_le]
      have h1N : 1 / N ≤ 1 := by rw [div_le_one hNpos]; exact hN1
      have h0N : 0 ≤ 1 / N := by positivity
      constructor <;> linarith [hp.1 x, hp_le x]
    calc t * |1 / N - p x| ≤ t * 1 := mul_le_mul_of_nonneg_left h1 ht0.le
      _ ≤ δ / 2 := by linarith
  obtain ⟨q, hq0, hq1, hqpos, hqnear⟩ := exists_rat_simplex_near p' hp' (half_pos hδ)
  have hqU : (fun x => (q x : ℝ)) ∈
      {p : ↥(WD D B) → ℝ | ∀ x, worldValue T (beliefHistory past) D B p x < ε} := by
    apply hball
    rw [Metric.mem_ball, dist_pi_lt_iff hδ]
    intro x
    rw [Real.dist_eq]
    calc |(q x : ℝ) - p x| = |((q x : ℝ) - p' x) + (p' x - p x)| := by ring_nf
      _ ≤ |(q x : ℝ) - p' x| + |p' x - p x| := abs_add_le _ _
      _ < δ / 2 + δ / 2 := add_lt_add_of_lt_of_le (hqnear x) (hp'near x)
      _ = δ := by ring
  refine ⟨extQ D B q, fun u hu => ?_, coherentAccepts_extQ_of_lt T past D B S hS ε q hq0 hq1 hqU⟩
  have h : extQ D B q u = q ⟨u, hu⟩ := by simp [extQ, hu]
  rw [h]
  exact hqpos _ (hp'pos _)

/-! ## T2(d): the customer's entry point -/

/-- **T2(d). The customer's entry point.** A coherently accepted weight vector bounds `T`'s value
by `ε` in **every `PCWorld` consistent with `D`**, on any real history `P` agreeing with the
candidate table on every cell `T` mentions (days `≤ n`), provided the traded sentences and the
stage are within the atom bound: restrict the world to `B` atoms (`WD D B`), then the exact
rational bound applies. This is the coherent twin of `bli-overlay`'s
`dayValue_le_of_accepted_state`, whose all-Boolean-tables hypothesis a coherent table cannot meet
(T4(a)); the agreement hypothesis is the wrong-market trap made explicit.
Source: [[bli-coherent-mm-mandate]] T2(d); [[bli-overlay-mandate]] T3(b)
Kind: L
Fidelity: exact
Hyps: (a) `hB` (atom bound on `T.support ∪ D`), `hacc`, `hagree` -/
theorem dayValue_le_of_coherentAccepts {n : ℕ} (T : Strategy n) (past : List RationalBeliefState)
    (D : Finset Sentence) (B : ℕ) (S : Finset Sentence) (hB : ∀ φ ∈ T.support ∪ D, atomBound φ ≤ B)
    {ε : ℚ} {w : FiniteWorld B → ℚ} (hacc : CoherentAccepts T past D B S ε w) (P : History)
    (hagree : ∀ φ, MentionedBy T φ → ∀ k ≤ n, P k φ = (candidateTable past n S w k φ : ℝ)) :
    ∀ v : PCWorld, v.ConsistentWith D → T.value P v.payout ≤ (ε : ℝ) := by
  intro v hv
  rw [value_payout_eq_restrict T P v (fun φ hφ => hB φ (Finset.mem_union_left _ hφ))]
  rw [Strategy.value_eq_of_eqOn_mentioned T P (fun k φ => (candidateTable past n S w k φ : ℝ)) _
    hagree]
  rw [T.value_eq_marketRatCast (fun k φ => (candidateTable past n S w k φ : ℝ))
    (candidateTable past n S w) (fun _ _ => rfl) (payoutReal _)
    (FiniteWorld.restrict (ofPCWorld v) B).payoutRat (fun _ => rfl)]
  exact_mod_cast hacc.2 _ (restrict_mem_WD (fun φ hφ => hB φ (Finset.mem_union_right _ hφ)) hv)

/-- **T2(d), split form**: agreement given separately on the mentioned past cells (`P` reads
`rationalHistory past`) and on the mentioned day-`n` cells (`P` reads `π w`; needs
`S ⊇ mentionedSet T`).
Source: [[bli-coherent-mm-mandate]] T2(d); [[bli-overlay-mandate]] §Lifecycle (split form)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem dayValue_le_of_coherentAccepts_split {n : ℕ} (T : Strategy n)
    (past : List RationalBeliefState) (D : Finset Sentence) (B : ℕ) (S : Finset Sentence)
    (hS : mentionedSet T ⊆ S) (hB : ∀ φ ∈ T.support ∪ D, atomBound φ ≤ B) {ε : ℚ}
    {w : FiniteWorld B → ℚ} (hacc : CoherentAccepts T past D B S ε w) (P : History)
    (hpast : ∀ φ, MentionedBy T φ → ∀ k < n, P k φ = (rationalHistory past k φ : ℝ))
    (hnow : ∀ φ, MentionedBy T φ → P n φ = (marginal w φ : ℝ)) :
    ∀ v : PCWorld, v.ConsistentWith D → T.value P v.payout ≤ (ε : ℝ) := by
  apply dayValue_le_of_coherentAccepts T past D B S hB hacc P
  intro φ hφ k hk
  rcases Nat.lt_or_eq_of_le hk with hk | rfl
  · rw [hpast φ hφ k hk, candidateTable_of_ne past hk.ne]
  · rw [hnow φ hφ, candidateTable_self_of_mem past k w (hS (mem_mentionedSet_iff.mpr hφ))]

end Cleanroom.Bli.BliCoherentMm.AttemptA
