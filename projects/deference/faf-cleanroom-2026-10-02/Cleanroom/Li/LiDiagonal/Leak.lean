import Cleanroom.Li.LiDiagonal.Defs
import LogicalInduction.Properties.Pseudorandomness

/-!
# `li-diagonal` · Leak: the revisiting leak (T6b)

**The revisiting leak** (vq-wiki-059/060): a `0/1` day-indicator weighting `W` supported on an
infinite set `E` of days on which `truth = 0`, with consecutive `E`-days separated by more than the
deferral `f`, is **divergent**, **`f`-patient** (at most one firing per window `[n, f n]`), and
witnesses that `truth` is **not** `PseudorandomFrequency` at any `p ≠ 0`: its weighted average of
`truth` is identically `0`. A standing warning: every "for every patient generable weighting"
hypothesis about revisited values is false.

The legality `hW : PGenerableWeighting W` of the indicator stream is a `MachineSpliceStream`
certificate; it is proved for the N+ instance `E := evens`, `f := succDeferral`
(`evenIndicator_pgenerable`, from FAF's `MachineDigits.mod_two`) and stays a parameter in the
general statement.

Scope: single-market (a statement about one market's legal weightings and one truth stream).
-/

namespace Cleanroom.Li.LiDiagonal

open LogicalInduction LO.Propositional
open Filter Topology

/-! ## The general leak -/

/-- **T6b (headline). The revisiting leak**: for `truth` vanishing on an infinite set `E` whose
consecutive days are `f`-separated (`∀ n < m ∈ E, f n < m`, `f` monotone), any legal weighting
`W` with `W_n = 𝟙[n ∈ E]` is divergent, `f`-patient, and refutes `PseudorandomFrequency truth p f P`
for every `p ≠ 0`.
Scope: single-market.
Source: [[vq-wiki-inventory]] 059, 060 (the revisiting leak); [[li-diagonal-mandate]] T6b
Kind: P
Fidelity: variant: exact zeros on `E` in place of vq-wiki-060(a)'s `Y_n → 0` on the revisited set; `Monotone f` added to the mandate's gap hypothesis
Hyps: (a) `hW` is the legality certificate of the indicator stream, proved for the instances; the rest is the day-set's shape -/
theorem revisiting_leak (P : History) (truth : ℕ → ℝ) (E : Set ℕ) [DecidablePred (· ∈ E)]
    (hinf : E.Infinite) (hzero : ∀ n ∈ E, truth n = 0) (f : DeferralFunction)
    (hmono : Monotone f.f) (hgap : ∀ n ∈ E, ∀ m ∈ E, n < m → f n < m)
    (W : ℕ → EF) (hW : PGenerableWeighting W)
    (hWE : ∀ n, (W n).denote P = if n ∈ E then 1 else 0) :
    DivergentWeighting W P ∧ DeferralPatient f W P ∧
      ∀ p : ℝ, p ≠ 0 → ¬ PseudorandomFrequency truth p f P := by
  set w : ℕ → ℝ := fun n => (W n).denote P with hw
  have h01 : ∀ n, 0 ≤ w n ∧ w n ≤ 1 := fun n => by
    simp only [hw, hWE]; split_ifs <;> norm_num
  have hmonoS : Monotone (prefixSum w) := monotone_nat_of_le_succ fun n => by
    simp only [prefixSum, Finset.sum_range_succ]
    linarith [(h01 (n + 1)).1]
  -- divergence: the prefix sums are unbounded
  have hdiv : DivergentWeighting W P := by
    refine ⟨h01, tendsto_atTop_atTop_of_monotone' hmonoS ?_⟩
    rintro ⟨C, hC⟩
    have hstep : ∀ k : ℕ, ∃ n, (k : ℝ) ≤ prefixSum w n := by
      intro k
      induction k with
      | zero => exact ⟨0, by simp only [prefixSum_zero, Nat.cast_zero]; exact (h01 0).1⟩
      | succ k ih =>
        obtain ⟨n, hn⟩ := ih
        obtain ⟨m, hmE, hnm⟩ := hinf.exists_gt n
        refine ⟨m, ?_⟩
        obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        have h1 : prefixSum w n ≤ prefixSum w m' := hmonoS (by omega)
        have h2 : prefixSum w (m' + 1) = prefixSum w m' + w (m' + 1) := by
          simp only [prefixSum, Finset.sum_range_succ]
        have h3 : w (m' + 1) = 1 := by simp only [hw, hWE, if_pos hmE]
        push_cast
        linarith
    obtain ⟨n, hn⟩ := hstep (Nat.ceil C + 1)
    have := hC (Set.mem_range_self n)
    have hceil : (C : ℝ) ≤ Nat.ceil C := Nat.le_ceil C
    push_cast at hn
    linarith
  refine ⟨hdiv, ?_, ?_⟩
  · -- patience: at most one `E`-day per window
    refine ⟨1, fun n => ?_⟩
    have hsum : ∑ i ∈ Finset.Icc n (f n), w i =
        ((Finset.Icc n (f n)).filter (· ∈ E)).card := by
      rw [Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hw, hWE]
      split_ifs <;> simp
    have hcard : ((Finset.Icc n (f n)).filter (· ∈ E)).card ≤ 1 := by
      refine Finset.card_le_one.2 fun i hi j hj => ?_
      simp only [Finset.mem_filter, Finset.mem_Icc] at hi hj
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · have := hgap i hi.2 j hj.2 hlt
        have := hmono hi.1.1
        omega
      · have := hgap j hj.2 i hi.2 hlt
        have := hmono hj.1.1
        omega
    change ∑ i ∈ Finset.Icc n (f n), w i ≤ 1
    rw [hsum]
    exact_mod_cast hcard
  · -- not pseudorandom at any nonzero `p`
    intro p hp hpr
    have hpat : DeferralPatient f W P := by
      refine ⟨1, fun n => ?_⟩
      have hsum : ∑ i ∈ Finset.Icc n (f n), w i =
          ((Finset.Icc n (f n)).filter (· ∈ E)).card := by
        rw [Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [hw, hWE]
        split_ifs <;> simp
      have hcard : ((Finset.Icc n (f n)).filter (· ∈ E)).card ≤ 1 := by
        refine Finset.card_le_one.2 fun i hi j hj => ?_
        simp only [Finset.mem_filter, Finset.mem_Icc] at hi hj
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hlt
        · have := hgap i hi.2 j hj.2 hlt
          have := hmono hi.1.1
          omega
        · have := hgap j hj.2 i hi.2 hlt
          have := hmono hj.1.1
          omega
      change ∑ i ∈ Finset.Icc n (f n), w i ≤ 1
      rw [hsum]
      exact_mod_cast hcard
    have havg := hpr W hW hdiv hpat
    have hzeroAvg : ∀ n, weightedAverage (fun i => (W i).denote P) truth n = 0 := by
      intro n
      unfold weightedAverage
      split_ifs with h
      · rfl
      · have : prefixSum (fun i => (W i).denote P * truth i) n = 0 := by
          unfold prefixSum
          refine Finset.sum_eq_zero fun i _ => ?_
          rw [hWE]
          split_ifs with hi
          · rw [hzero i hi, mul_zero]
          · rw [zero_mul]
        rw [this, zero_div]
    unfold AsympEq at havg
    simp only [hzeroAvg, zero_sub] at havg
    have := tendsto_nhds_unique havg (tendsto_const_nhds (x := -p))
    exact hp (neg_eq_zero.mp this.symm)

/-! ## The N+ instance: the even days under the successor deferral -/

/-- The even-day indicator as a constant-leaf feature stream.
Source: [[li-diagonal-mandate]] T6b (`E := evens`)
Kind: D
Fidelity: exact
Hyps: n/a -/
def evenIndicator (n : ℕ) : EF := EF.const (if Even n then 1 else 0)

/-- `evenIndicator_denote`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem evenIndicator_denote (P : History) (n : ℕ) :
    (evenIndicator n).denote P = if n ∈ {m : ℕ | Even m} then 1 else 0 := by
  unfold evenIndicator
  rw [EF.denote_const]
  simp only [Set.mem_setOf_eq]
  split_ifs <;> simp

/-- **The even-day indicator is a legal feature progression**: its constant leaf's code is the
unary-ruler computable `⌜1⌝·((n+1) mod 2) + ⌜0⌝·(n mod 2)` (FAF's `MachineDigits.mod_two`,
`UnaryRuler.add/mul`), hence a `MachineSpliceStream` via `serialize_const_write`.
Source: [[li-diagonal-mandate]] T6b (the legality certificate of a `0/1` day-indicator stream)
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem evenIndicator_pgenerable : PGenerableWeighting evenIndicator := by
  have h1 : UnaryRuler (fun n : ℕ => (n + 1) % 2) :=
    (MachineDigits.ofUnaryRuler UnaryRuler.id.succ).mod_two
  have h0 : UnaryRuler (fun n : ℕ => n % 2) :=
    (MachineDigits.ofUnaryRuler UnaryRuler.id).mod_two
  have hr : UnaryRuler (fun n : ℕ =>
      Encodable.encode (1 : ℚ) * ((n + 1) % 2) + Encodable.encode (0 : ℚ) * (n % 2)) :=
    ((UnaryRuler.const _).mul h1).add ((UnaryRuler.const _).mul h0)
  have hdig : MachineDigits (fun n : ℕ => Encodable.encode (if Even n then (1 : ℚ) else 0)) := by
    refine (MachineDigits.ofUnaryRuler hr).of_eq fun n => ?_
    rcases Nat.even_or_odd n with he | ho
    · rw [if_pos he]
      have h1' : (n + 1) % 2 = 1 := by
        rw [Nat.even_iff] at he; omega
      have h0' : n % 2 = 0 := by rw [Nat.even_iff] at he; exact he
      rw [h1', h0']; ring
    · rw [if_neg (Nat.not_even_iff_odd.mpr ho)]
      have h1' : (n + 1) % 2 = 0 := by
        rw [Nat.odd_iff] at ho; omega
      have h0' : n % 2 = 1 := by rw [Nat.odd_iff] at ho; exact ho
      rw [h1', h0']; ring
  refine { polySeg := MachineSpliceStream.serialize_const_write hdig, rank_le := ?_, closed := ?_ }
  · intro n; simp [evenIndicator]
  · intro n ρ V; simp [evenIndicator, EF.denoteWith, EF.denote]

/-- **The revisiting leak on the even days** (N+): any `truth` vanishing on the even days is not
`PseudorandomFrequency` at any `p ≠ 0` under `succDeferral`, witnessed by the legal, divergent,
`succ`-patient even-day indicator. The patience conjunct is trivial at `succ` (every weighting
bounded by `1` is `succ`-patient, `succPatient_of_le_one`): N+ for divergence and the
identically-zero weighted average, N− for patience (audit r2 adversarial N3).
Scope: single-market; deferral `n ↦ n+1`.
Source: [[vq-wiki-inventory]] 059, 060; [[li-diagonal-mandate]] T6b instance
Kind: N+ (divergence, zero average); N− (patience, trivial at `succ`)
Fidelity: exact
Hyps: (a) none -/
theorem revisiting_leak_evens (P : History) (truth : ℕ → ℝ)
    (hzero : ∀ n, Even n → truth n = 0) :
    DivergentWeighting evenIndicator P ∧ DeferralPatient succDeferral evenIndicator P ∧
      ∀ p : ℝ, p ≠ 0 → ¬ PseudorandomFrequency truth p succDeferral P := by
  classical
  refine revisiting_leak P truth {m : ℕ | Even m} ?_ (fun n hn => hzero n hn) succDeferral
    (fun a b hab => Nat.succ_le_succ hab) ?_ evenIndicator evenIndicator_pgenerable
    (evenIndicator_denote P)
  · exact Set.infinite_of_injective_forall_mem (f := fun k => 2 * k)
      (fun a b h => by simpa using h) (fun k => even_two_mul k)
  · intro n hn m hm hnm
    change n + 1 < m
    simp only [Set.mem_setOf_eq] at hn hm
    rcases Nat.lt_or_ge (n + 1) m with h | h
    · exact h
    · exfalso
      have : m = n + 1 := by omega
      subst this
      exact Nat.even_add_one.mp hm hn

/-! ## The patience clause at `succDeferral` is trivial (repair round 2) -/

/-- **Every weighting bounded by `1` is `succDeferral`-patient** (repair round 2; audit r2
adversarial N3, probe `SuccPatienceTrivial.lean`): the window `[n, n+1]` has two days. So the
patience conjunct of `revisiting_leak_evens` carries no content at `succ` — that witness is N+ for
divergence and the identically-zero weighted average, N− for patience. The source's leak is
"patient *by sparsity*" under a fast deferral such as `2^n`, where the uniform weighting is *not*
patient (`const_one_not_doublingPatient`); the sparse instance that would exercise the clause (a
tower-sparse day set under `doublingDeferral`, whose indicator needs a ruler certificate FAF's
combinators do not obviously give) is not built.
Scope: single-market; deferral `n ↦ n+1`.
Source: none: infrastructure (grading of `revisiting_leak_evens`)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem succPatient_of_le_one (P : History) (W : ℕ → EF) (h : ∀ n, (W n).denote P ≤ 1) :
    DeferralPatient succDeferral W P := by
  refine ⟨2, fun n => ?_⟩
  have hcard : (Finset.Icc n (succDeferral n)).card = 2 := by
    show (Finset.Icc n (n + 1)).card = 2
    rw [Nat.card_Icc]; omega
  calc ∑ i ∈ Finset.Icc n (succDeferral n), (W i).denote P
      ≤ (Finset.Icc n (succDeferral n)).card • (1 : ℝ) :=
        Finset.sum_le_card_nsmul _ _ _ (fun i _ => h i)
    _ = 2 := by rw [hcard]; norm_num

/-- The uniform weighting is `succ`-patient (contrast `const_one_not_doublingPatient` at `2^n`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem const_one_succPatient (P : History) :
    DeferralPatient succDeferral (fun _ => EF.const 1) P :=
  succPatient_of_le_one P _ (fun _ => by simp)

end Cleanroom.Li.LiDiagonal
