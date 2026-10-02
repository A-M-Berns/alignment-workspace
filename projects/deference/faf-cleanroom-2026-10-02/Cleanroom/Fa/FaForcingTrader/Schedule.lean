import Cleanroom.Fa.FaForcingTrader.Defs
import Cleanroom.Fa.FaTheoremA.Analysis

/-!
# `fa-forcing-trader` · Schedule: the interleaved deferral function and the N+ schedules (T2)

Shared by both angles (written by angle A). The `H`-side Kelly round trip of FAF
(`feedbackTrader`) opens component `k` at `g k` and closes it at `g (k+1)` along **one** strictly
increasing deferral function `g`. v3's schedule "buy at `d k`, sell at `f (d k)`" is rendered by
**interleaving**: `g (2k) = d k`, `g (2k+1) = f (d k)`; on the odd rungs the weighting is `0`
(the lookahead day is never a scheduled day, `WindowDisjoint.lookahead_not_mem`), so the trader
is idle there and every live round trip is exactly v3's.

* `interleave f d h : DeferralFunction` — the function, its deferral (`2k < d k` from
  window-disjointness), and its `graph_fp`: the graph `g n = m` is decided by scanning `k ≤ m`
  for `n = 2k ∧ d k = m` or `n = 2k+1 ∧ d k ≤ m ∧ f (d k) = m`, every test a FAF `UnaryRuler`
  (`graphFlag_ruler`, `unaryRuler_scheduledValue`, `segPrefix`), so the class is *inhabited*, not
  merely assumed (T2's trap).
* `interleave_strictMono`, `interleave_apply_even/odd`, the support transfer
  `interleave_supported`, and the two facts T4's re-indexing needs.
* `linearSchedule c` (`d k = (c+2)(k+1)`) — N+ schedules, window-disjoint for `succDeferral`
  with no side condition; `scheduleIndicator_divergent`.
* The tower schedule `d (k+1) = 2^{d k}` for `f = doublingDeferral` is **not built** (stretch);
  nothing here depends on it.
-/

namespace Cleanroom.Fa.FaForcingTrader

open LogicalInduction Cleanroom.Fa.FaTheoremA Cleanroom.Found.LiQuoteLane
  Cleanroom.Found.LiAsympCalc Cleanroom.Found.DefLattice Filter Topology

/-! ## A. The interleaved function and its graph decider -/

/-- `g (2k) = d k`, `g (2k+1) = f (d k)`.
Source: mandate T2 ("rendered as one `DeferralFunction` by interleaving")
Kind: D
Fidelity: exact
Hyps: n/a -/
def interleaveFn (f d : DeferralFunction) (n : ℕ) : ℕ :=
  if n % 2 = 0 then d.f (n / 2) else f.f (d.f (n / 2))

/-- Even rung.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem interleaveFn_even (f d : DeferralFunction) (j : ℕ) :
    interleaveFn f d (j + j) = d.f j := by
  unfold interleaveFn
  have h1 : (j + j) % 2 = 0 := by omega
  have h2 : (j + j) / 2 = j := by omega
  rw [if_pos h1, h2]

/-- Odd rung.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem interleaveFn_odd (f d : DeferralFunction) (j : ℕ) :
    interleaveFn f d (j + j + 1) = f.f (d.f j) := by
  unfold interleaveFn
  have h1 : (j + j + 1) % 2 ≠ 0 := by omega
  have h2 : (j + j + 1) / 2 = j := by omega
  rw [if_neg h1, h2]

/-- One summand of the graph scan at the paired index `⟨⟨n, m⟩, k⟩`: `1` when
`n = 2k ∧ d k = m`, or when `n = 2k+1`, `d k ≤ m` and `f (d k) = m` (the value `d k` read off
FAF's day-bounded lookup `scheduledValue`, which is `0` when `d k > m`, and `d k ≥ 1` always);
`0` otherwise. Every operation is a `UnaryRuler` combinator (`interleaveTerm_ruler`).
Source: mandate T2 ("`graph_fp` from the two graph deciders"); FAF `scheduledValue`
Kind: D
Fidelity: n/a
Hyps: n/a -/
def interleaveTerm (f d : DeferralFunction) (w : ℕ) : ℕ :=
  (if w.unpair.1.unpair.1 = w.unpair.2 + w.unpair.2 then 1 else 0) *
      d.graphFlag (Nat.pair w.unpair.2 w.unpair.1.unpair.2) +
    (if w.unpair.1.unpair.1 = w.unpair.2 + w.unpair.2 + 1 then 1 else 0) *
      ((scheduledValue d (Nat.pair w.unpair.1.unpair.2 w.unpair.2) -
          (scheduledValue d (Nat.pair w.unpair.1.unpair.2 w.unpair.2) - 1)) *
        f.graphFlag (Nat.pair (scheduledValue d (Nat.pair w.unpair.1.unpair.2 w.unpair.2))
          w.unpair.1.unpair.2))

/-- The summand is machine-metered on the unary paired index.
Source: mandate T2; FAF `DeferralFunction.graphFlag_ruler`, `unaryRuler_scheduledValue`
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem interleaveTerm_ruler (f d : DeferralFunction) : UnaryRuler (interleaveTerm f d) := by
  have hn : UnaryRuler (fun w : ℕ => w.unpair.1.unpair.1) :=
    UnaryRuler.unpairFst.comp UnaryRuler.unpairFst
  have hm : UnaryRuler (fun w : ℕ => w.unpair.1.unpair.2) :=
    UnaryRuler.unpairSnd.comp UnaryRuler.unpairFst
  have hk : UnaryRuler (fun w : ℕ => w.unpair.2) := UnaryRuler.unpairSnd
  have hsv : UnaryRuler
      (fun w : ℕ => scheduledValue d (Nat.pair w.unpair.1.unpair.2 w.unpair.2)) :=
    (unaryRuler_scheduledValue d).comp (hm.pair hk)
  have hterm1 : UnaryRuler (fun w : ℕ =>
      (if w.unpair.1.unpair.1 = w.unpair.2 + w.unpair.2 then 1 else 0) *
        d.graphFlag (Nat.pair w.unpair.2 w.unpair.1.unpair.2)) :=
    (hn.eqFlag (hk.add hk)).mul (d.graphFlag_ruler.comp (hk.pair hm))
  have hterm2 : UnaryRuler (fun w : ℕ =>
      (if w.unpair.1.unpair.1 = w.unpair.2 + w.unpair.2 + 1 then 1 else 0) *
        ((scheduledValue d (Nat.pair w.unpair.1.unpair.2 w.unpair.2) -
            (scheduledValue d (Nat.pair w.unpair.1.unpair.2 w.unpair.2) - 1)) *
          f.graphFlag (Nat.pair (scheduledValue d (Nat.pair w.unpair.1.unpair.2 w.unpair.2))
            w.unpair.1.unpair.2))) :=
    (hn.eqFlag ((hk.add hk).succ)).mul
      ((hsv.sub (hsv.sub (UnaryRuler.const 1))).mul (f.graphFlag_ruler.comp (hsv.pair hm)))
  exact (hterm1.add hterm2).of_eq (fun w => rfl)

/-- The scan of a summand family over `k < r` vanishes iff every summand does.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem segPrefix_eq_zero_iff (lenFn : ℕ → ℕ) (N : ℕ) :
    ∀ r, segPrefix lenFn N r = 0 ↔ ∀ k < r, lenFn (Nat.pair N k) = 0
  | 0 => by simp
  | r + 1 => by
      rw [segPrefix_succ, Nat.add_eq_zero_iff, segPrefix_eq_zero_iff lenFn N r]
      constructor
      · rintro ⟨h1, h2⟩ k hk
        rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
        · exact h1 k hk
        · exact h2
      · intro h
        exact ⟨fun k hk => h k (Nat.lt_succ_of_lt hk), h r (Nat.lt_succ_self r)⟩

/-- The summand at `⟨⟨n, m⟩, k⟩` is nonzero exactly in the two intended cases.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem interleaveTerm_ne_zero_iff (f d : DeferralFunction) (n m k : ℕ) :
    interleaveTerm f d (Nat.pair (Nat.pair n m) k) ≠ 0 ↔
      (n = k + k ∧ d.f k = m) ∨ (n = k + k + 1 ∧ d.f k ≤ m ∧ f.f (d.f k) = m) := by
  have hdk : 0 < d.f k := Nat.lt_of_le_of_lt (Nat.zero_le k) (d.lt k)
  simp only [interleaveTerm, Nat.unpair_pair, DeferralFunction.graphFlag, scheduledValue_eq_ite]
  by_cases h1 : n = k + k
  · have h2 : n ≠ k + k + 1 := by omega
    by_cases h3 : d.f k = m <;> simp [h1, h3]
  · by_cases h2 : n = k + k + 1
    · by_cases h4 : d.f k ≤ m
      · by_cases h5 : f.f (d.f k) = m
        · simp [h2, h4, h5]
          omega
        · simp [h2, h4, h5]
      · simp [h2, h4]
    · simp [h1, h2]

/-- The graph count at `⟨n, m⟩`: the scan over `k ≤ m`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def interleaveCount (f d : DeferralFunction) (z : ℕ) : ℕ :=
  segPrefix (interleaveTerm f d) z (z.unpair.2 + 1)

/-- The count is machine-metered on the unary pair.
Source: mandate T2; FAF `UnaryRuler.segPrefix`
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem interleaveCount_ruler (f d : DeferralFunction) : UnaryRuler (interleaveCount f d) :=
  ((UnaryRuler.segPrefix (interleaveTerm_ruler f d)).comp
    (UnaryRuler.id.pair UnaryRuler.unpairSnd.succ)).of_eq (fun z => by simp [interleaveCount])

/-- The count vanishes iff `g n ≠ m`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem interleaveCount_eq_zero_iff (f d : DeferralFunction) (n m : ℕ) :
    interleaveCount f d (Nat.pair n m) = 0 ↔ interleaveFn f d n ≠ m := by
  unfold interleaveCount
  rw [Nat.unpair_pair, segPrefix_eq_zero_iff]
  constructor
  · intro h hnm
    rcases Nat.even_or_odd' n with ⟨j, rfl | rfl⟩
    · rw [show 2 * j = j + j by ring, interleaveFn_even] at hnm
      have hj : j < m + 1 := by
        have := d.lt j
        omega
      exact (interleaveTerm_ne_zero_iff f d (2 * j) m j).2 (Or.inl ⟨by ring, hnm⟩) (h j hj)
    · rw [show 2 * j + 1 = j + j + 1 by ring, interleaveFn_odd] at hnm
      have hfd := f.lt (d.f j)
      have hj : j < m + 1 := by
        have := d.lt j
        omega
      exact (interleaveTerm_ne_zero_iff f d (2 * j + 1) m j).2
        (Or.inr ⟨by ring, by omega, hnm⟩) (h j hj)
  · intro h k _
    by_contra hk
    rcases (interleaveTerm_ne_zero_iff f d n m k).1 hk with ⟨rfl, hd⟩ | ⟨rfl, -, hf⟩
    · exact h (by rw [interleaveFn_even]; exact hd)
    · exact h (by rw [interleaveFn_odd]; exact hf)

/-- **T2: the interleaved schedule as a deferral function.** `g (2k) = d k`, `g (2k+1) = f (d k)`;
it defers because a window-disjoint `d` satisfies `d k > 2k`; its graph is decided in polynomial
time on the unary pair by `interleaveCount`.
Source: mandate T2; vq-wiki-046 Lemma 1 (c)/(d) (the parts `graph_fp` renders)
Kind: P
Fidelity: exact
Hyps: (a) none -/
def interleave (f d : DeferralFunction) (h : WindowDisjoint f d) : DeferralFunction where
  f := interleaveFn f d
  lt := fun n => by
    rcases Nat.even_or_odd' n with ⟨j, rfl | rfl⟩
    · rw [show 2 * j = j + j by ring, interleaveFn_even]
      have := h.two_mul_lt j
      omega
    · rw [show 2 * j + 1 = j + j + 1 by ring, interleaveFn_odd]
      have := h.two_mul_lt j
      have := f.lt (d.f j)
      omega
  graph_fp :=
    ⟨fun z => List.replicate (if interleaveCount f d z.length = 0 then 0 else 1) false,
      (interleaveCount_ruler f d).ifZero (UnaryRuler.const 0) (UnaryRuler.const 1),
      fun n m => by
        simp only [List.length_replicate]
        by_cases hc : interleaveCount f d (Nat.pair n m) = 0
        · rw [if_pos hc, if_neg ((interleaveCount_eq_zero_iff f d n m).1 hc)]
        · rw [if_neg hc, if_pos (not_not.1 ((interleaveCount_eq_zero_iff f d n m).not.1 hc))]⟩

/-- Even rung of the interleaving.
Source: mandate T2
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem interleave_apply_even {f d : DeferralFunction} (h : WindowDisjoint f d) (k : ℕ) :
    (interleave f d h).f (2 * k) = d.f k := by
  show interleaveFn f d (2 * k) = d.f k
  rw [show 2 * k = k + k by ring, interleaveFn_even]

/-- Odd rung of the interleaving.
Source: mandate T2
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem interleave_apply_odd {f d : DeferralFunction} (h : WindowDisjoint f d) (k : ℕ) :
    (interleave f d h).f (2 * k + 1) = f.f (d.f k) := by
  show interleaveFn f d (2 * k + 1) = f.f (d.f k)
  rw [show 2 * k + 1 = k + k + 1 by ring, interleaveFn_odd]

/-- **T2: the interleaving is strictly increasing** (FAF's `StrictlyIncreasingDeferral`, the
schedule condition of `thm:wubaff` and of the feedback trader).
Source: mandate T2; FAF `StrictlyIncreasingDeferral`
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem interleave_strictMono {f d : DeferralFunction} (h : WindowDisjoint f d) :
    StrictlyIncreasingDeferral (interleave f d h) := by
  refine strictMono_nat_of_lt_succ (fun n => ?_)
  rcases Nat.even_or_odd' n with ⟨j, rfl | rfl⟩
  · show (interleave f d h).f (2 * j) < (interleave f d h).f (2 * j + 1)
    rw [interleave_apply_even, interleave_apply_odd]
    exact f.lt _
  · show (interleave f d h).f (2 * j + 1) < (interleave f d h).f (2 * j + 1 + 1)
    rw [interleave_apply_odd, show 2 * j + 1 + 1 = 2 * (j + 1) by ring, interleave_apply_even]
    exact h.2 j

/-- After an even rung the next rung is the lookahead of the current day: the live round trip
"buy at `d k`, sell at `f (d k)`".
Source: mandate T4 ("re-index from `g`'s indices to days")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem interleave_succ_of_even {f d : DeferralFunction} (h : WindowDisjoint f d) {i : ℕ}
    (hi : i % 2 = 0) : (interleave f d h).f (i + 1) = f.f ((interleave f d h).f i) := by
  obtain ⟨j, rfl⟩ : ∃ j, i = 2 * j := ⟨i / 2, by omega⟩
  rw [interleave_apply_even, interleave_apply_odd]

/-- An odd rung is never a scheduled day (so a weighting supported on `im d` vanishes there: the
trader is idle on the odd rungs).
Source: mandate T4 ("the odd rungs contribute `0`")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem interleave_not_mem_of_odd {f d : DeferralFunction} (h : WindowDisjoint f d) {i : ℕ}
    (hi : i % 2 = 1) (k : ℕ) : d.f k ≠ (interleave f d h).f i := by
  obtain ⟨j, rfl⟩ : ∃ j, i = 2 * j + 1 := ⟨i / 2, by omega⟩
  rw [interleave_apply_odd]
  exact h.lookahead_not_mem j k

/-- A weighting supported on `im d` is supported on the image of the interleaving.
Source: mandate T4 (the support transfer)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem interleave_supported {f d : DeferralFunction} (h : WindowDisjoint f d) {w : ℕ → ℝ}
    (hw : ∀ n, w n ≠ 0 → ∃ k, d.f k = n) : ∀ n, w n ≠ 0 → ∃ j, (interleave f d h).f j = n := by
  intro n hn
  obtain ⟨k, hk⟩ := hw n hn
  exact ⟨2 * k, by rw [interleave_apply_even]; exact hk⟩

/-! ## B. The N+ schedules -/

/-- **The linear schedules** `d k = (c + 2) · (k + 1)`: deferral functions (graph decided by one
affine comparison on the unary pair), window-disjoint for `succDeferral` with no side condition
(gaps `c + 2 ≥ 2`). `linearSchedule 0` is `2, 4, 6, …`.
Source: mandate T2 (`linearSchedule c`, "any `c ≥ 2`", here reparametrised so every instance is window-disjoint)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
def linearSchedule (c : ℕ) : DeferralFunction where
  f k := (c + 2) * k + (c + 2)
  lt k := by
    have := Nat.le_mul_of_pos_left k (show 0 < c + 2 by omega)
    omega
  graph_fp :=
    ⟨fun z => List.replicate
        (if (c + 2) * z.length.unpair.1 + (c + 2) = z.length.unpair.2 then 1 else 0) false,
      UnaryRuler.eqFlag (((UnaryRuler.const (c + 2)).mul UnaryRuler.unpairFst).add
        (UnaryRuler.const (c + 2))) UnaryRuler.unpairSnd,
      fun n m => by simp⟩

/-- `linearSchedule c k = (c + 2) k + (c + 2)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem linearSchedule_apply (c k : ℕ) : (linearSchedule c).f k = (c + 2) * k + (c + 2) := rfl

/-- **Every linear schedule is window-disjoint for the successor lookahead.**
Source: mandate T2 (N+ schedule)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem windowDisjoint_succ_linear (c : ℕ) : WindowDisjoint succDeferral (linearSchedule c) := by
  rw [windowDisjoint_succ]
  intro k
  rw [linearSchedule_apply, linearSchedule_apply, Nat.mul_succ]
  omega

/-- **The bare schedule indicator is a divergent weighting** in every market: it is `{0,1}`-valued
and carries weight `1` on the infinitely many days `d k`.
Source: mandate T4 witness ("`G := scheduleIndicator d` (mass divergent)")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem scheduleIndicator_divergent (d : DeferralFunction) (P : History) :
    DivergentWeighting (scheduleIndicator d) P := by
  refine ⟨fun n => scheduleIndicator_mem_Icc d P n, ?_⟩
  refine tendsto_prefixSum_atTop_of_frequently_one (fun n => (scheduleIndicator_mem_Icc d P n).1) ?_
  rw [frequently_atTop]
  intro a
  refine ⟨d.f a, (d.lt a).le, ?_⟩
  rw [scheduleIndicator_denote, schedInd_of_mem]

end Cleanroom.Fa.FaForcingTrader
