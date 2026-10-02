import Cleanroom.Bli.BliExtrapolation.Witnesses

/-!
# `bli-extrapolation` · Decay: PDF 06's decay scheme is the ½-rule (target 4c(ii))

PDF 06 p. 2 eq. (1) proposes, for a universal `U = ∀mφ(m)` whose instances beyond `m` are left
to the rule, the decay `P(φ(1) ∧ … ∧ φ(k)) := P(U) + r / 2^{k−m}` for `k ≥ m`, with
`r = P(φ(1) ∧ … ∧ φ(m)) − P(U)`. This file proves that under the halving hypotheses of target 4b
(`HalvingCondition`: infinitely many instances are fresh atoms at increasing levels `k 0 < k 1 < …`
undecided on every `Ax`-consistent `¬U`-conjunction) `sotoRule` *produces* exactly that decay:

* `decay_scheme_pow`: `P(⋀_{j<n} a_j) = P(U) + (½)^n · P(¬U)` for every `n`, where `a_j` is the
  instance at the `j`-th halving level;
* `decay_scheme_is_half_rule` (the mandate's display): for `m ≤ n`,
  `P(⋀_{j<n} a_j) = P(U) + (P(⋀_{j<m} a_j) − P(U)) / 2^{n−m}`;
* `decay_scheme_of_halvingCondition`: the same, packaged under `HalvingCondition`.

The two ingredients are the halving step `negUnivPrefix_val_succ` (`Gaifman.lean`), iterated to
`negUnivPrefix_val_pow`, and the nullity of `U ∧ ¬a_j` (schema 1 almost everywhere,
`extrapolateVal_neg_ax`), which gives `P(U ∧ ⋀_{j<n} a_j) = P(U)`
(`extrapolateVal_univ_and_instPrefix`). The prefix is `⋀_{j<n}` (indices from `0`); the source's
display mixes `φ(0)` and `φ(1)` as the first index (finding F-4).

**Witness** (`decay_witness`, N+): on the 4b witness (`halvingS`, `freshEnum`, `halvingBase`) the
identity at `n = 1` reads `P(a_0) = P(U) + ½ · P(¬U)`; both sides are computed independently of
this file's theorems (`¾` by `halving_val_inst0`, `½ + ½·½` by `halving_val_univ` and
`halving_val_neg_univ`) and agree, with the correction term `¼ ≠ 0`.

Sources: PDF 06 p. 2 eq. (1); [[bli-soto-a-inventory]] 052 (ii); [[bli-soto-a-2-inventory]]
"Verification" (confirms the display and notes the index mix).
-/

namespace Cleanroom.Bli.BliExtrapolation

open LogicalInduction LO.Propositional BoolPCWorld Finset

/-! ## Prefix conjunctions -/

/-- `a 0 ⋏ … ⋏ a (n-1)`, left-nested from `⊤`: the conjunction of the first `n` sentences of a
family (PDF 06's `φ(1) ∧ … ∧ φ(k)`, indexed from `0`).
Source: PDF 06 p. 2 (`φ(1) ∧ … ∧ φ(k)`)
Kind: D
Fidelity: exact (indices from `0`; the source mixes `φ(0)` and `φ(1)`, F-4) -/
def instPrefix (a : ℕ → Sentence) : ℕ → Sentence
  | 0 => ⊤
  | n + 1 => instPrefix a n ⋏ a n

/-- A world holds `instPrefix a n` iff it holds `a j` for every `j < n`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma holds_instPrefix_iff (a : ℕ → Sentence) (v : PCWorld) :
    ∀ n, v.Holds (instPrefix a n) ↔ ∀ j < n, v.Holds (a j)
  | 0 => by simp [instPrefix, PCWorld.holds_top]
  | n + 1 => by
      rw [instPrefix, PCWorld.holds_and, holds_instPrefix_iff a v n]
      constructor
      · rintro ⟨h1, h2⟩ j hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · exact h1 j hj
        · exact h2
      · intro h
        exact ⟨fun j hj => h j (Nat.lt_succ_of_lt hj), h n (Nat.lt_succ_self n)⟩

/-- `negUnivPrefix U a n` is `∼U ⋏ instPrefix (atom ∘ a) n` in every world.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma holds_negUnivPrefix_iff (U : Sentence) (a : ℕ → ℕ) (v : PCWorld) :
    ∀ n, v.Holds (negUnivPrefix U a n) ↔
      v.Holds (∼U ⋏ instPrefix (fun j => Formula.atom (a j)) n)
  | 0 => by simp [negUnivPrefix, instPrefix, PCWorld.holds_and, PCWorld.holds_top]
  | n + 1 => by
      rw [negUnivPrefix, instPrefix]
      simp only [PCWorld.holds_and]
      rw [holds_negUnivPrefix_iff U a v n]
      simp only [PCWorld.holds_and]
      tauto

/-! ## The decay scheme -/

section Decay

variable (S : UnivStructure) [∀ Γ φ, Decidable (AxEntails S Γ φ)] (e : ℕ ≃ ℕ) {B : ℕ}

/-- The halving step iterated: under the halving hypotheses of `negUnivPrefix_val_succ`,
`P(¬U ∧ a_0 ∧ … ∧ a_{n−1}) = (½)^n · P(¬U)` (the `hval` step of `gaifman_eq_of_halving`, as a
lemma of its own).
Source: PIBBSS §4.3 p. 18 ("the infinite multiplication by 1/2"); PDF 06 p. 2 eq. (1)
Kind: P
Fidelity: exact -/
theorem negUnivPrefix_val_pow (q : FiniteWorld B → ℚ) (u : ℕ) (hq0 : ∀ w, 0 ≤ q w)
    (hq1 : ∑ w, q w = 1) (hbase : BaseAxConsistent S e q) (k : ℕ → ℕ) (hk : StrictMono k)
    (hkB : B ≤ k 0) (hlev : level e (S.univSentence u) ≤ k 0)
    (hhalf : ∀ n (w : FiniteWorld (k n)), AxConsistent S {conj e w} →
      ¬ (enumWorld e w).toPCWorld.Holds (S.univSentence u) →
      ¬ AxEntails S {conj e w} (Formula.atom (e (k n))) ∧
        ¬ AxEntails S {conj e w} (∼Formula.atom (e (k n)))) :
    ∀ n, extrapolateVal S e q (negUnivPrefix (S.univSentence u) (fun n => e (k n)) n) =
      (1 / 2) ^ n * extrapolateVal S e q (∼S.univSentence u)
  | 0 => by simp [negUnivPrefix]
  | n + 1 => by
      rw [negUnivPrefix_val_succ S e q u hq0 hq1 hbase k hk hkB hlev hhalf n,
        negUnivPrefix_val_pow q u hq0 hq1 hbase k hk hkB hlev hhalf n]
      ring

/-- `U ∧ ¬inst u j` is null: the negation of the schema-1 axiom `U 🡒 inst u j` has value zero
(`extrapolateVal_neg_ax`), and `U ⋏ ∼inst u j` is that negation in every world.
Source: none: infrastructure (schema 1 almost everywhere)
Kind: L
Fidelity: n/a -/
lemma extrapolateVal_univ_and_neg_inst (q : FiniteWorld B → ℚ) (hq0 : ∀ w, 0 ≤ q w)
    (hq1 : ∑ w, q w = 1) (hbase : BaseAxConsistent S e q) (u j : ℕ) :
    extrapolateVal S e q (S.univSentence u ⋏ ∼S.inst u j) = 0 := by
  have hax : S.univSentence u 🡒 S.inst u j ∈ Ax S := by
    left; left; exact ⟨u, j, rfl⟩
  have h0 := extrapolateVal_neg_ax S e hq0 hq1 hbase hax
  unfold extrapolateVal at h0 ⊢
  rw [← h0]
  apply chainVal_congr
  intro v
  rw [PCWorld.holds_and, PCWorld.holds_neg, PCWorld.holds_neg, holds_imp]
  tauto

/-- `P(U ∧ ⋀_{j<n} inst u (i j)) = P(U)` for every index map `i`: each instance is implied by `U`
almost everywhere (schema 1), so adding instances under `U` costs no mass.
Source: PDF 07 p. 2 (schema 1); PDF 06 p. 2
Kind: P
Fidelity: exact -/
theorem extrapolateVal_univ_and_instPrefix (q : FiniteWorld B → ℚ) (hq0 : ∀ w, 0 ≤ q w)
    (hq1 : ∑ w, q w = 1) (hbase : BaseAxConsistent S e q) (u : ℕ) (i : ℕ → ℕ) :
    ∀ n, extrapolateVal S e q (S.univSentence u ⋏ instPrefix (fun j => S.inst u (i j)) n) =
      extrapolateVal S e q (S.univSentence u)
  | 0 => by
      unfold extrapolateVal
      apply chainVal_congr
      intro v
      simp [instPrefix, PCWorld.holds_and, PCWorld.holds_top]
  | n + 1 => by
      have ih := extrapolateVal_univ_and_instPrefix q hq0 hq1 hbase u i n
      rw [← ih]
      unfold extrapolateVal
      have hunit := sotoRule_inUnit S e hq0
      have hzero : chainVal e (sotoRule S e q)
          (∼S.inst u (i n) ⋏ (S.univSentence u ⋏ instPrefix (fun j => S.inst u (i j)) n)) = 0 := by
        apply le_antisymm _ (chainVal_mem_Icc e hunit _).1
        have h0 := extrapolateVal_univ_and_neg_inst S e q hq0 hq1 hbase u (i n)
        unfold extrapolateVal at h0
        rw [← h0]
        apply chainVal_mono e hunit
        intro v hv
        rw [PCWorld.holds_and, PCWorld.holds_and] at hv
        exact (PCWorld.holds_and _ _ _).mpr ⟨hv.2.1, hv.1⟩
      rw [chainVal_split e (sotoRule S e q) (S.inst u (i n))
        (S.univSentence u ⋏ instPrefix (fun j => S.inst u (i j)) n), hzero, add_zero]
      apply chainVal_congr
      intro v
      simp only [instPrefix, PCWorld.holds_and]
      tauto

/-- **4c(ii), `decay_scheme_pow`**: under the halving hypotheses (the unpacked `HalvingCondition`,
with its level map `k` and index map `i`), the prefix conjunctions of the instances at the halving
levels decay geometrically to `P(U)`: `P(⋀_{j<n} inst u (i j)) = P(U) + (½)^n · P(¬U)`.
Proof: split along `U`; under `U` the instances cost nothing (`extrapolateVal_univ_and_instPrefix`);
under `¬U` each halving level halves (`negUnivPrefix_val_pow`).
Source: PDF 06 p. 2 eq. (1); [[bli-soto-a-inventory]] 052 (ii)
Kind: P
Fidelity: exact (prefix `j < n` over the instances at the halving levels, indices from `0`)
Hyps: (a) `0 ≤ q`, `∑ q = 1`, `BaseAxConsistent`; (a) the halving hypotheses (discharged by
`halving_witness`, and by `halving_of_fresh_instances` for any fresh-instance structure) -/
theorem decay_scheme_pow (q : FiniteWorld B → ℚ) (u : ℕ) (hq0 : ∀ w, 0 ≤ q w)
    (hq1 : ∑ w, q w = 1) (hbase : BaseAxConsistent S e q) (k i : ℕ → ℕ) (hk : StrictMono k)
    (hkB : B ≤ k 0) (hlev : level e (S.univSentence u) ≤ k 0)
    (hinst : ∀ n, S.inst u (i n) = Formula.atom (e (k n)))
    (hhalf : ∀ n (w : FiniteWorld (k n)), AxConsistent S {conj e w} →
      ¬ (enumWorld e w).toPCWorld.Holds (S.univSentence u) →
      ¬ AxEntails S {conj e w} (Formula.atom (e (k n))) ∧
        ¬ AxEntails S {conj e w} (∼Formula.atom (e (k n)))) (n : ℕ) :
    extrapolateVal S e q (instPrefix (fun j => S.inst u (i j)) n) =
      extrapolateVal S e q (S.univSentence u) +
        (1 / 2) ^ n * extrapolateVal S e q (∼S.univSentence u) := by
  rw [← extrapolateVal_univ_and_instPrefix S e q hq0 hq1 hbase u i n,
    ← negUnivPrefix_val_pow S e q u hq0 hq1 hbase k hk hkB hlev hhalf n]
  unfold extrapolateVal
  rw [chainVal_split e (sotoRule S e q) (S.univSentence u)
    (instPrefix (fun j => S.inst u (i j)) n)]
  congr 1
  simp only [hinst]
  apply chainVal_congr
  intro v
  rw [holds_negUnivPrefix_iff]

/-- **4c(ii), `decay_scheme_is_half_rule`** (the mandate's display; PDF 06 eq. (1)): under the
halving hypotheses, for `m ≤ n`,
`P(⋀_{j<n} inst u (i j)) = P(U) + (P(⋀_{j<m} inst u (i j)) − P(U)) / 2^{n−m}`:
the decay scheme is what `sotoRule` produces, with `r = P(⋀_{j<m}) − P(U) = (½)^m · P(¬U)`.
Source: PDF 06 p. 2 eq. (1); [[bli-soto-a-inventory]] 052 (ii); [[bli-soto-a-2-inventory]]
"Verification"
Kind: P
Fidelity: exact (prefix `j < n` over the instances at the halving levels; the source's display
mixes `φ(0)` and `φ(1)` as the first index, F-4)
Hyps: (a) `0 ≤ q`, `∑ q = 1`, `BaseAxConsistent`; (a) the halving hypotheses (discharged by
`halving_witness`) -/
theorem decay_scheme_is_half_rule (q : FiniteWorld B → ℚ) (u : ℕ) (hq0 : ∀ w, 0 ≤ q w)
    (hq1 : ∑ w, q w = 1) (hbase : BaseAxConsistent S e q) (k i : ℕ → ℕ) (hk : StrictMono k)
    (hkB : B ≤ k 0) (hlev : level e (S.univSentence u) ≤ k 0)
    (hinst : ∀ n, S.inst u (i n) = Formula.atom (e (k n)))
    (hhalf : ∀ n (w : FiniteWorld (k n)), AxConsistent S {conj e w} →
      ¬ (enumWorld e w).toPCWorld.Holds (S.univSentence u) →
      ¬ AxEntails S {conj e w} (Formula.atom (e (k n))) ∧
        ¬ AxEntails S {conj e w} (∼Formula.atom (e (k n)))) {m n : ℕ} (hmn : m ≤ n) :
    extrapolateVal S e q (instPrefix (fun j => S.inst u (i j)) n) =
      extrapolateVal S e q (S.univSentence u) +
        (extrapolateVal S e q (instPrefix (fun j => S.inst u (i j)) m) -
          extrapolateVal S e q (S.univSentence u)) / 2 ^ (n - m) := by
  rw [decay_scheme_pow S e q u hq0 hq1 hbase k i hk hkB hlev hinst hhalf n,
    decay_scheme_pow S e q u hq0 hq1 hbase k i hk hkB hlev hinst hhalf m]
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [Nat.add_sub_cancel_left, pow_add]
  simp only [one_div_pow]
  ring

/-- `decay_scheme_is_half_rule` packaged under `HalvingCondition`: along the condition's level map
`k` and index map `i`, the display holds for all `m ≤ n`.
Source: PDF 06 p. 2 eq. (1); [[bli-soto-a-inventory]] 052 (ii)
Kind: C
Fidelity: exact (as `decay_scheme_is_half_rule`)
Hyps: (a) `0 ≤ q`, `∑ q = 1`, `BaseAxConsistent`; (a) `HalvingCondition` (discharged by
`halving_witness`) -/
theorem decay_scheme_of_halvingCondition (q : FiniteWorld B → ℚ) (u : ℕ) (hq0 : ∀ w, 0 ≤ q w)
    (hq1 : ∑ w, q w = 1) (hbase : BaseAxConsistent S e q) (h : HalvingCondition S e B u) :
    ∃ k i : ℕ → ℕ, StrictMono k ∧ (∀ n, S.inst u (i n) = Formula.atom (e (k n))) ∧
      ∀ m n, m ≤ n → extrapolateVal S e q (instPrefix (fun j => S.inst u (i j)) n) =
        extrapolateVal S e q (S.univSentence u) +
          (extrapolateVal S e q (instPrefix (fun j => S.inst u (i j)) m) -
            extrapolateVal S e q (S.univSentence u)) / 2 ^ (n - m) := by
  obtain ⟨k, i, hk, hkB, hlev, hinst, hhalf⟩ := h
  exact ⟨k, i, hk, hinst, fun m n hmn =>
    decay_scheme_is_half_rule S e q u hq0 hq1 hbase k i hk hkB hlev hinst hhalf hmn⟩

end Decay

/-! ## Witness: the 4b witness exercises the identity -/

open Classical in
/-- **Witness for 4c(ii)** (N+): on the 4b witness (`halvingS`, `freshEnum`, `halvingBase`, index
map `id`, whose halving hypotheses `halving_witness` discharges) the identity at `n = 1` reads
`P(a_0) = P(U) + ½ · P(¬U)`. Both sides are computed here *independently* of this file's theorems:
the right side is `½ + ½·½ = ¾` by `halving_val_univ` and `halving_val_neg_univ`, the left side is
`¾` by `halving_val_inst0` (`instPrefix … 1 = ⊤ ⋏ a_0`). They agree, and the correction term
`½ · P(¬U) = ¼` is not zero, so the identity is exercised, not idle.
Source: mandate 4c(ii); PDF 06 p. 2 eq. (1)
Kind: N+
Fidelity: n/a
Hyps: (a) none (all discharged) -/
theorem decay_witness :
    extrapolateVal halvingS freshEnum halvingBase (halvingS.univSentence 0) +
        (1 / 2) ^ 1 * extrapolateVal halvingS freshEnum halvingBase (∼halvingS.univSentence 0) =
      3 / 4 ∧
    extrapolateVal halvingS freshEnum halvingBase (instPrefix (fun j => halvingS.inst 0 j) 1) =
      3 / 4 := by
  refine ⟨by rw [halving_val_univ, halving_val_neg_univ]; norm_num, ?_⟩
  rw [← halving_val_inst0]
  unfold extrapolateVal
  apply chainVal_congr
  intro v
  simp [instPrefix, PCWorld.holds_and, PCWorld.holds_top]

end Cleanroom.Bli.BliExtrapolation
