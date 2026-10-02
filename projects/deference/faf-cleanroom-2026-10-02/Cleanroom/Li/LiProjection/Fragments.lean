import Cleanroom.Li.LiProjection.LemmaA
import Cleanroom.Li.LiProjection.Marginal
import LogicalInduction.Properties.NonDogmatism
import LogicalInduction.Properties.Relationships

/-!
# `li-projection` · Fragments: limits on the decided and undecided fragments (T4)

Package `Cleanroom.Li.LiProjection` ([[li-projection-mandate]]), file 10 of the layout.

* **T4.1 Decided fragment.** Two inductors over the same process agree asymptotically on every
  efficiently computable family the completed theory decides (`decided_fragment_agree`, provability
  induction twice); the day-set form along a ruler-decidable set of days
  (`decided_fragment_agree_daySet`); and the single-sentence biconditionals
  `limitingBelief P φ = 1 ↔` every completed-theory world holds `φ` (`limitingBelief_eq_one_iff`),
  dually for `0` — both directions derived (provability induction one way, non-dogmatism the other).
* **T4.2 A trader confined to an undecided sentence.** The mandate's rendering (i) — "for *any*
  history with `P n φ + P n (∼φ) = 1`, a trader all of whose trades are on `φ` or `∼φ` cannot
  exploit" — is **false**: `confined_exploits_oscillating` exhibits an exactly coherent pricing of
  `φ` that oscillates between `9/10` and `1/10` and a `φ`-confined trader (sell `10/9` shares on even
  days, buy `10` on odd days) whose net worth is bounded below in both `φ`-worlds and unbounded
  above in the `φ`-world. What *is* true without the criterion is the time-constant form
  (`confined_not_exploits_const`: `P n φ = p ∈ (0,1)` for all `n`, exact coherence, both worlds
  plausible). With the criterion the statement is trivial (`noExploit`, kind T, no row). The
  flagged converse (iii): the buy-both trader exploits any pricing with `P n φ + P n (∼φ) ≤ 1 − ε`
  (`buyBoth_exploits`, with its efficiency certificate; N− `buyBoth_exploits_quarterP` here, N+
  `buyBoth_exploits_oscGapP_paper` in `Witnesses.lean` on the oscillating `oscGapP` over
  `paperDP 𝗜𝚺₁`). An N− witness for Lemma A's exploitation transfer (`combo_exploits_zeroP`) is
  at the end of the T4.2 section.
* **T4.3 Achievable limits on a fresh atom.** Every inductor's limiting belief on a fresh atom
  lies in the open interval `(0,1)` and is coherent with its negation
  (`limitingBelief_atom_mem_Ioo`, `limitingBelief_atom_add_neg`), and every *rational* `c ∈ (0,1)`
  is attained (`achievable_limits_fresh_atom_rat`, given any inductor over `DP` to project — the
  LIA instance is in `Witnesses.lean`). The set is squeezed between `ℚ ∩ (0,1)` and `(0,1)`; the
  irrational case needs a weight with infinitely many jumps (OPEN T7.5).
* **Jeffrey-form finite-jump manipulation** (`jeffrey_steering_finiteJumps`): Lemma A with the
  weight jumping once, to `c*`.
-/

namespace Cleanroom.Li.LiProjection

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Filter Topology

/-! ## T4.1 The decided fragment -/

/-- **Decided fragment: limits agree.** Two inductors over the same `DP` agree asymptotically on an
efficiently computable family that the completed theory decides positively (provability induction
for each).
Source: [[anson-2-inventory]] 004(i); [[deference-in-logical-induction-v6]] §5.6 T7(i); [[root-deference-inventory]] 044(i)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem decided_fragment_agree (P P' : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    [IsLogicalInductor P' DP] (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (φ : ℕ → Sentence) (hφ : MachineSentenceCodes φ)
    (hthm : ∀ n, ∀ v : PCWorld, v.ConsistentWithTheory DP → v.Holds (φ n)) :
    (fun n => P n (φ n)) ≈ₙ (fun n => P' n (φ n)) :=
  (lic_provind_true P DP φ hφ hthm hworld).trans (lic_provind_true P' DP φ hφ hthm hworld).symm

/-- Decided fragment, refuted side: the two inductors agree on a family the theory refutes.
Source: [[anson-2-inventory]] 004(i)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem refuted_fragment_agree (P P' : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    [IsLogicalInductor P' DP] (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (φ : ℕ → Sentence) (hφ : MachineSentenceCodes φ)
    (hdis : ∀ n, ∀ v : PCWorld, v.ConsistentWithTheory DP → v.Holds (∼φ n)) :
    (fun n => P n (φ n)) ≈ₙ (fun n => P' n (φ n)) :=
  (lic_provind_false P DP φ hφ hdis hworld).trans (lic_provind_false P' DP φ hφ hdis hworld).symm

/-- **Decided fragment along a ruler-decidable day-set.** For `G := {n | t n = 0}` with `t` a
unary ruler (an `FP`-decidable indicator on the unary day) and an e.c. family `φ` decided by the
theory on `G`, the restricted family `φ' n := if t n = 0 then φ n else ⊤` is e.c. and the two
inductors agree asymptotically on it — hence, along `G`, on `φ` itself.
Source: [[deference-in-logical-induction-v6]] §5.6 T7(i) on an e.c. day-set; [[root-deference-inventory]] 044(i)
Kind: C
Fidelity: exact (the day-set is rendered as the zero set of a unary ruler)
Hyps: (a) -/
theorem decided_fragment_agree_daySet (P P' : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] [IsLogicalInductor P' DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (t : ℕ → ℕ) (ht : UnaryRuler t)
    (φ : ℕ → Sentence) (hφ : MachineSentenceCodes φ)
    (hthm : ∀ n, t n = 0 → ∀ v : PCWorld, v.ConsistentWithTheory DP → v.Holds (φ n)) :
    ((fun n => P n (if t n = 0 then φ n else ⊤)) ≈ₙ
        (fun n => P' n (if t n = 0 then φ n else ⊤))) ∧
      ∀ ε > 0, ∀ᶠ n in atTop, t n = 0 → |P n (φ n) - P' n (φ n)| < ε := by
  have hcodes : MachineSentenceCodes (fun n => if t n = 0 then φ n else ⊤) :=
    MachineSentenceCodes.ifZero hφ (MachineSentenceCodes.const _) ht
  have hdec : ∀ n, ∀ v : PCWorld, v.ConsistentWithTheory DP →
      v.Holds (if t n = 0 then φ n else ⊤) := by
    intro n v hv
    by_cases h : t n = 0
    · rw [if_pos h]; exact hthm n h v hv
    · rw [if_neg h]; exact PCWorld.holds_top v
  have hag := decided_fragment_agree P P' DP hworld _ hcodes hdec
  refine ⟨hag, fun ε hε => ?_⟩
  have := (Metric.tendsto_atTop.mp hag) ε hε
  obtain ⟨N, hN⟩ := this
  refine Filter.eventually_atTop.mpr ⟨N, fun n hn h0 => ?_⟩
  have := hN n hn
  simp only [if_pos h0, Real.dist_eq, sub_zero] at this
  exact this

/-- **The single-sentence biconditional.** `limitingBelief P φ = 1` iff every completed-theory world
holds `φ`: provability induction at the constant family one way, non-dogmatism (a completed-theory
world falsifying `φ` is consistent with every stage) the other.
Source: [[anson-2-inventory]] 004(i); mandate T4.1 (also what T6.2 needs)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem limitingBelief_eq_one_iff (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (φ : Sentence) :
    limitingBelief P φ = 1 ↔ ∀ v : PCWorld, v.ConsistentWithTheory DP → v.Holds φ := by
  constructor
  · intro h1
    by_contra hnot
    push_neg at hnot
    obtain ⟨v, hv, hvφ⟩ := hnot
    obtain ⟨L, hL, hL1⟩ := lic_exists_limit_lt_one P DP φ (fun n => ⟨v, hv n, hvφ⟩)
    have : limitingBelief P φ = L := hL.limsup_eq
    linarith
  · intro hthm
    have h := lic_provind_true P DP (fun _ => φ) (MachineSentenceCodes.const φ)
      (fun _ v hv => hthm v hv) hworld
    exact (tendsto_sub_nhds_zero_iff.mp h).limsup_eq

/-- Dual: `limitingBelief P φ = 0` iff every completed-theory world falsifies `φ`.
Source: [[anson-2-inventory]] 004(i)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem limitingBelief_eq_zero_iff (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (φ : Sentence) :
    limitingBelief P φ = 0 ↔ ∀ v : PCWorld, v.ConsistentWithTheory DP → ¬ v.Holds φ := by
  constructor
  · intro h0
    by_contra hnot
    push_neg at hnot
    obtain ⟨v, hv, hvφ⟩ := hnot
    obtain ⟨L, hL, hL0⟩ := lic_exists_limit_pos P DP φ (fun n => ⟨v, hv n, hvφ⟩)
    have : limitingBelief P φ = L := hL.limsup_eq
    linarith
  · intro hdis
    have h := lic_provind_false P DP (fun _ => φ) (MachineSentenceCodes.const φ)
      (fun _ v hv => by rw [PCWorld.holds_neg]; exact hdis v hv) hworld
    exact (tendsto_sub_nhds_zero_iff.mp h).limsup_eq

/-! ## T4.2 A trader confined to an undecided sentence -/

/-- The process with empty stages: every world is consistent with every stage (the N+ carrier for
statements that quantify over arbitrary histories).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def trivialDP : DeductiveProcess := ⟨fun _ => ∅, fun _ => subset_rfl⟩

/-- `trivialDP_consistentWith`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma trivialDP_consistentWith (v : PCWorld) (n : ℕ) : v.ConsistentWith (trivialDP.D n) :=
  fun φ h => absurd h (Finset.notMem_empty φ)

/-- A payout identity: in any world, the payouts of `φ` and `∼φ` sum to `1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma payout_add_payout_neg (v : PCWorld) (φ : Sentence) : v.payout φ + v.payout (∼φ) = 1 := by
  unfold PCWorld.payout
  by_cases h : v.Holds φ
  · rw [if_pos h, if_neg (by rw [PCWorld.holds_neg]; exact fun h' => h' h)]; ring
  · rw [if_neg h, if_pos (by rw [PCWorld.holds_neg]; exact h)]; ring

/-- **The time-constant confined-trader lemma.** For *any* history `P` (no criterion) pricing `φ` at
a constant `p ∈ (0,1)` and `∼φ` at `1 − p`, with both `φ`-verdicts plausible at every stage, no
trader all of whose trades are on `φ` or `∼φ` exploits `P`: the price-weighted sum of its net worths
in a `φ`-world and a `¬φ`-world is `0` on every day, so bounded below in both forces bounded above.
Source: [[lean-deference-inventory]] 076 (origin chat msg 10, corrected: exact coherence *and* a constant price — the exact-coherence-only form is refuted below)
Kind: P
Fidelity: weaker: the price of `φ` is constant in time (necessary without the criterion, `confined_exploits_oscillating`)
Hyps: (a) -/
theorem confined_not_exploits_const (P : History) (DP : DeductiveProcess) (φ : Sentence) (p : ℝ)
    (hp0 : 0 < p) (hp1 : p < 1) (hp : ∀ n, P n φ = p) (hp' : ∀ n, P n (∼φ) = 1 - p)
    (hboth : ∀ n, (∃ v : PCWorld, v.ConsistentWith (DP.D n) ∧ v.Holds φ) ∧
      (∃ v : PCWorld, v.ConsistentWith (DP.D n) ∧ ¬ v.Holds φ))
    (T : Trader) (hT : ∀ n, ∀ q ∈ (T.strat n).trades, q.2 = φ ∨ q.2 = ∼φ) :
    ¬ T.Exploits P DP := by
  rintro ⟨⟨L, hL⟩, hnotAbove⟩
  have hval : ∀ n (v v' : PCWorld), v.Holds φ → ¬ v'.Holds φ →
      p * (T.strat n).value P v.payout + (1 - p) * (T.strat n).value P v'.payout = 0 := by
    intro n v v' hv hv'
    simp only [Strategy.value]
    rw [← List.sum_map_mul_left, ← List.sum_map_mul_left, ← List.sum_map_add]
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
    have hvneg : ¬ v.Holds (∼φ) := by rw [PCWorld.holds_neg]; exact fun h => h hv
    have hv'neg : v'.Holds (∼φ) := by rw [PCWorld.holds_neg]; exact hv'
    rcases hT n q hq with h | h
    · rw [h, hp n]
      simp only [PCWorld.payout, if_pos hv, if_neg hv']
      ring
    · rw [h, hp' n]
      simp only [PCWorld.payout, if_neg hvneg, if_pos hv'neg]
      ring
  have hnet : ∀ n (v v' : PCWorld), v.Holds φ → ¬ v'.Holds φ →
      p * T.netWorth P v n + (1 - p) * T.netWorth P v' n = 0 := by
    intro n v v' hv hv'
    unfold Trader.netWorth
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun m _ => hval m v v' hv hv'
  apply hnotAbove
  refine ⟨max (-(1 - p) * L / p) (-p * L / (1 - p)), ?_⟩
  rintro x ⟨n, w, hw, rfl⟩
  obtain ⟨⟨v, hv, hvφ⟩, ⟨v', hv', hv'φ⟩⟩ := hboth n
  by_cases hwφ : w.Holds φ
  · have h0 := hnet n w v' hwφ hv'φ
    have hL' := hL ⟨n, v', hv', rfl⟩
    refine le_max_of_le_left ?_
    rw [le_div_iff₀ hp0]
    nlinarith
  · have h0 := hnet n v w hvφ hwφ
    have hL' := hL ⟨n, v, hv, rfl⟩
    refine le_max_of_le_right ?_
    rw [le_div_iff₀ (by linarith)]
    nlinarith

/-! ### The exact-coherence-only form is false -/

/-- A world holding every atom (in particular `φ := atom 0`).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def worldTrue : PCWorld := fun _ => True

/-- A world falsifying every atom.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def worldFalse : PCWorld := fun _ => False

/-- An exactly coherent pricing of the atom `0` that oscillates: `9/10` on even days, `1/10` on odd
days, with `∼atom 0` priced complementarily and everything else at `1/2`.
Source: mandate T4.2 (the counterexample to its rendering (i))
Kind: D
Fidelity: n/a -/
noncomputable def oscP : History := fun n ψ =>
  if ψ = Formula.atom 0 then (if n % 2 = 0 then (9 : ℝ) / 10 else 1 / 10)
  else if ψ = ∼Formula.atom 0 then (if n % 2 = 0 then (1 : ℝ) / 10 else 9 / 10) else 1 / 2

/-- The trader confined to the atom `0`: sell `10/9` shares on even days, buy `10` on odd days.
Source: mandate T4.2 (the counterexample)
Kind: D
Fidelity: n/a -/
def oscT : Trader where
  strat n := { trades := [(EF.const (if n % 2 = 0 then -10 / 9 else 10), Formula.atom 0)],
               rank_le := by simp }

/-- `oscP_atom`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma oscP_atom (n : ℕ) : oscP n (Formula.atom 0) = if n % 2 = 0 then (9 : ℝ) / 10 else 1 / 10 := by
  simp [oscP]

/-- `oscP_neg_atom`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma oscP_neg_atom (n : ℕ) :
    oscP n (∼Formula.atom 0) = if n % 2 = 0 then (1 : ℝ) / 10 else 9 / 10 := by
  have hne : (∼Formula.atom 0 : Sentence) ≠ Formula.atom 0 := fun h => by cases h
  simp [oscP, hne]

/-- `oscP` is exactly coherent on the atom `0`.
Source: mandate T4.2
Kind: L
Fidelity: n/a -/
lemma oscP_coherent (n : ℕ) : oscP n (Formula.atom 0) + oscP n (∼Formula.atom 0) = 1 := by
  rw [oscP_atom, oscP_neg_atom]
  split_ifs <;> norm_num

/-- `oscT_value_true`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma oscT_value_true (i : ℕ) :
    (oscT.strat i).value oscP worldTrue.payout = if i % 2 = 0 then -(1 : ℝ) / 9 else 9 := by
  have h : worldTrue.payout (Formula.atom 0) = 1 := by
    simp [PCWorld.payout, worldTrue, PCWorld.Holds, Formula.Boolean.val]
  simp only [oscT, Strategy.value, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    EF.denote_const, h, oscP_atom]
  split_ifs <;> norm_num

/-- `oscT_value_false`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma oscT_value_false (i : ℕ) :
    (oscT.strat i).value oscP worldFalse.payout = if i % 2 = 0 then (1 : ℝ) else -1 := by
  have h : worldFalse.payout (Formula.atom 0) = 0 := by
    simp [PCWorld.payout, worldFalse, PCWorld.Holds, Formula.Boolean.val]
  simp only [oscT, Strategy.value, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    EF.denote_const, h, oscP_atom]
  split_ifs <;> norm_num

/-- `oscT_netWorth_true`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma oscT_netWorth_true : ∀ m : ℕ,
    oscT.netWorth oscP worldTrue (2 * m) = m * (80 / 9) - 1 / 9 ∧
    oscT.netWorth oscP worldTrue (2 * m + 1) = (m + 1) * (80 / 9) := by
  intro m
  induction m with
  | zero =>
      simp only [Trader.netWorth, Nat.mul_zero, zero_add, Finset.sum_range_succ,
        Finset.sum_range_zero, oscT_value_true]
      norm_num
  | succ m ih =>
      obtain ⟨ih0, ih1⟩ := ih
      have e1 : 2 * (m + 1) = 2 * m + 1 + 1 := by ring
      have e2 : 2 * (m + 1) + 1 = 2 * m + 1 + 1 + 1 := by ring
      constructor
      · rw [e1]
        unfold Trader.netWorth at ih1 ⊢
        rw [Finset.sum_range_succ, ih1, oscT_value_true]
        rw [if_pos (by omega)]
        push_cast; ring
      · rw [e2]
        unfold Trader.netWorth at ih1 ⊢
        rw [Finset.sum_range_succ, Finset.sum_range_succ, ih1, oscT_value_true, oscT_value_true]
        rw [if_pos (by omega), if_neg (by omega)]
        push_cast; ring

/-- `oscT_netWorth_false`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma oscT_netWorth_false : ∀ m : ℕ,
    oscT.netWorth oscP worldFalse (2 * m) = 1 ∧ oscT.netWorth oscP worldFalse (2 * m + 1) = 0 := by
  intro m
  induction m with
  | zero =>
      simp only [Trader.netWorth, Nat.mul_zero, zero_add, Finset.sum_range_succ,
        Finset.sum_range_zero, oscT_value_false]
      norm_num
  | succ m ih =>
      obtain ⟨ih0, ih1⟩ := ih
      have e1 : 2 * (m + 1) = 2 * m + 1 + 1 := by ring
      have e2 : 2 * (m + 1) + 1 = 2 * m + 1 + 1 + 1 := by ring
      constructor
      · rw [e1]
        unfold Trader.netWorth at ih1 ⊢
        rw [Finset.sum_range_succ, ih1, oscT_value_false, if_pos (by omega)]
        ring
      · rw [e2]
        unfold Trader.netWorth at ih1 ⊢
        rw [Finset.sum_range_succ, Finset.sum_range_succ, ih1, oscT_value_false, oscT_value_false,
          if_pos (by omega), if_neg (by omega)]
        ring

/-- A trader confined to the atom `0` has, in any world holding the atom, the net worth it has in
`worldTrue`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma oscT_netWorth_eq_true (w : PCWorld) (hw : w.Holds (Formula.atom 0)) (n : ℕ) :
    oscT.netWorth oscP w n = oscT.netWorth oscP worldTrue n := by
  unfold Trader.netWorth
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [oscT, Strategy.value, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  have hw' : w 0 := hw
  have : w.payout (Formula.atom 0) = worldTrue.payout (Formula.atom 0) := by
    simp [PCWorld.payout, hw', worldTrue, PCWorld.Holds, Formula.Boolean.val]
  rw [this]

/-- In any world falsifying the atom, the confined trader has the net worth it has in `worldFalse`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma oscT_netWorth_eq_false (w : PCWorld) (hw : ¬ w.Holds (Formula.atom 0)) (n : ℕ) :
    oscT.netWorth oscP w n = oscT.netWorth oscP worldFalse n := by
  unfold Trader.netWorth
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [oscT, Strategy.value, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  have hw' : ¬ w 0 := hw
  have : w.payout (Formula.atom 0) = worldFalse.payout (Formula.atom 0) := by
    simp [PCWorld.payout, hw', worldFalse, PCWorld.Holds, Formula.Boolean.val]
  rw [this]

/-- **Refutation of the exact-coherence-only confined-trader claim.** Over the empty process (every
world plausible at every stage), the exactly coherent oscillating pricing `oscP` is exploited by
the `atom 0`-confined trader `oscT`: bounded below by `−1/9` in every world, unbounded above in the
`atom 0`-world. So "a trader confined to an undecided sentence cannot exploit an exactly coherent
pricing" is false without the criterion (or a time-constant price); limit coherence is not what
blocks the arbitrage — the criterion is.
Source: mandate T4.2(i) (its rendering is refuted); [[lean-deference-inventory]] 076 (sharpened); [[lean-deference-2-inventory]] 032(b) ("coherence pins only `P_∞(φ) + P_∞(∼φ) = 1`")
Kind: P
Fidelity: exact (a counterexample to the universal statement)
Hyps: (a) -/
theorem confined_exploits_oscillating :
    (∀ n, oscP n (Formula.atom 0) + oscP n (∼Formula.atom 0) = 1) ∧
    (∀ n, (∃ v : PCWorld, v.ConsistentWith (trivialDP.D n) ∧ v.Holds (Formula.atom 0)) ∧
      (∃ v : PCWorld, v.ConsistentWith (trivialDP.D n) ∧ ¬ v.Holds (Formula.atom 0))) ∧
    (∀ n, ∀ q ∈ (oscT.strat n).trades, q.2 = Formula.atom 0) ∧
    oscT.Exploits oscP trivialDP := by
  refine ⟨oscP_coherent, fun n => ⟨⟨worldTrue, trivialDP_consistentWith _ _, trivial⟩,
    ⟨worldFalse, trivialDP_consistentWith _ _, fun h => h⟩⟩, ?_, ?_⟩
  · intro n q hq
    simp only [oscT, List.mem_singleton] at hq
    rw [hq]
  · refine ⟨⟨-(1 : ℝ) / 9, ?_⟩, ?_⟩
    · rintro x ⟨n, w, -, rfl⟩
      have hm0 : (0 : ℝ) ≤ (Nat.even_or_odd' n).choose := Nat.cast_nonneg _
      obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' n
      · subst hm
        by_cases hw : w.Holds (Formula.atom 0)
        · rw [oscT_netWorth_eq_true w hw, (oscT_netWorth_true m).1]
          nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
        · rw [oscT_netWorth_eq_false w hw, (oscT_netWorth_false m).1]
          norm_num
      · subst hm
        by_cases hw : w.Holds (Formula.atom 0)
        · rw [oscT_netWorth_eq_true w hw, (oscT_netWorth_true m).2]
          nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
        · rw [oscT_netWorth_eq_false w hw, (oscT_netWorth_false m).2]
          norm_num
    · rintro ⟨B, hB⟩
      obtain ⟨m, hm⟩ := exists_nat_gt B
      have hx := hB ⟨2 * m + 1, worldTrue, trivialDP_consistentWith _ _, rfl⟩
      rw [(oscT_netWorth_true m).2] at hx
      nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

/-! ### The flagged converse: the buy-both trader -/

/-- The trader buying one share each of `φ` and `∼φ` every day.
Source: [[lean-deference-inventory]] 076 (the inventory's flag)
Kind: D
Fidelity: exact -/
def buyBoth (φ : Sentence) : Trader where
  strat _ := { trades := [(EF.const 1, φ), (EF.const 1, ∼φ)], rank_le := by simp }

/-- `buyBoth φ` is efficiently computable (two trades per day, FAF's `ofTradeBlocksBig`).
Source: FAF `APITests` pattern; mandate T4.2(iii)
Kind: L
Fidelity: exact -/
theorem buyBoth_ec (φ : Sentence) : EfficientlyComputable (buyBoth φ) :=
  EfficientlyComputable.ofTradeBlocksBig _ (fun _ => 2) (fun _ => EF.const 1)
    (fun z => if z.unpair.2 = 0 then φ else ∼φ) (UnaryRuler.const 2)
    (MachineSpliceStream.ofPriceFree (MachineTokenStream.const (EF.const 1).serialize)
      (fun _ => trivial))
    (MachineSentenceCodes.ifZero (MachineSentenceCodes.const φ) (MachineSentenceCodes.const (∼φ))
      UnaryRuler.unpairSnd)
    (fun n => by simp [buyBoth, Nat.unpair_pair, List.range_succ])

/-- **The buy-both trader exploits a pricing whose `P n φ + P n (∼φ)` stays `≤ 1 − ε`**: it banks at
least `ε` every day in every world. (Kind P; the inventory's flag on lean-deference-076.)
Source: [[lean-deference-inventory]] 076 (flag: "the buy-both trader *does* exploit a pricing whose `P(φ)+P(¬φ)` stays away from `1`")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem buyBoth_exploits (P : History) (DP : DeductiveProcess)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (φ : Sentence) (ε : ℝ) (hε : 0 < ε)
    (hgap : ∀ n, P n φ + P n (∼φ) ≤ 1 - ε) : (buyBoth φ).Exploits P DP := by
  refine exploits_of_ge_partialSums (buyBoth φ) P DP (fun _ => ε) ε hε (fun _ => hε.le) ?_
    (Filter.Eventually.frequently (Filter.Eventually.of_forall fun _ => le_rfl)) hworld
  intro n v _
  unfold Trader.netWorth
  apply Finset.sum_le_sum
  intro i _
  simp only [buyBoth, Strategy.value, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    EF.denote_const]
  have := payout_add_payout_neg v φ
  have := hgap i
  push_cast
  linarith

/-- The explicit history every sentence of which is priced `1/4`: `P φ + P ∼φ = 1/2 ≤ 1 − 1/2`.
Source: mandate T4.2(iii) ("N+ on an explicit history")
Kind: D
Fidelity: n/a -/
noncomputable def quarterP : History := fun _ _ => 1 / 4

/-- **N− for `buyBoth_exploits`**: the buy-both trader exploits `quarterP` over the empty process.
Degenerate (audit r1, fidelity B2 / adversarial 4): a pricing constant in time and in the sentence,
over a process with no sentences — it shows the hypotheses are satisfiable, nothing more. The
non-degenerate witness is `buyBoth_exploits_oscGapP_paper` (`Witnesses.lean`): a pricing that
oscillates in time and depends on the sentence, over FAF's paper process `paperDP 𝗜𝚺₁`.
Source: mandate T4.2(iii)
Kind: N-
Fidelity: exact -/
theorem buyBoth_exploits_quarterP : (buyBoth (Formula.atom 0)).Exploits quarterP trivialDP :=
  buyBoth_exploits quarterP trivialDP (fun n => ⟨worldTrue, trivialDP_consistentWith _ _⟩) _
    (1 / 2) (by norm_num) (fun _ => by simp [quarterP]; norm_num)

/-- A pricing with a persistent coherence gap that is **not** constant: `atom 0` at `3/8` on even
days and `1/8` on odd days, `∼atom 0` the other way round, everything else at `1/2`; so
`P n (atom 0) + P n (∼atom 0) = 1/2` on every day while both prices oscillate.
Source: audit r1 (fidelity) B2 (the suggested non-constant witness)
Kind: D
Fidelity: n/a -/
noncomputable def oscGapP : History := fun n ψ =>
  if ψ = Formula.atom 0 then (if n % 2 = 0 then (3 : ℝ) / 8 else 1 / 8)
  else if ψ = ∼Formula.atom 0 then (if n % 2 = 0 then (1 : ℝ) / 8 else 3 / 8) else 1 / 2

/-- `oscGapP_sum`: the coherence gap is `1/2` on every day.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma oscGapP_sum (n : ℕ) : oscGapP n (Formula.atom 0) + oscGapP n (∼Formula.atom 0) = 1 / 2 := by
  have hne : (∼Formula.atom 0 : Sentence) ≠ Formula.atom 0 := fun h => by cases h
  simp only [oscGapP, if_true, hne, if_false]
  split_ifs <;> norm_num

/-- `oscGapP` is not constant in time (its price of `atom 0` on day `0` differs from day `1`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma oscGapP_not_const : oscGapP 0 (Formula.atom 0) ≠ oscGapP 1 (Formula.atom 0) := by
  simp [oscGapP]; norm_num

/-! ### An N− witness for the exploitation transfer -/

/-- The zero history: every sentence priced `0` on every day.
Source: audit r1 (adversarial) 3 (the suggested witness for `combo_exploits_of_exploits`)
Kind: D
Fidelity: n/a -/
noncomputable def zeroP : History := fun _ _ => 0

/-- The projection of the zero history is the zero history.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma project_zeroP (u : ℕ) (q : ℕ → ℚ) (n : ℕ) (φ : Sentence) : project zeroP u q n φ = 0 := by
  simp [project_apply, zeroP]

/-- The buy-`⊤`-daily trader exploits the projection of the zero history over the empty process:
it banks `1` every day in every world.
Source: audit r1 (adversarial) 3
Kind: L
Fidelity: n/a -/
theorem buyDaily_top_exploits_project_zeroP (u : ℕ) (q : ℕ → ℚ) :
    (buyDaily ⊤).Exploits (project zeroP u q) trivialDP := by
  refine exploits_of_ge_partialSums (buyDaily ⊤) _ trivialDP (fun _ => 1) 1 one_pos
    (fun _ => zero_le_one) ?_
    (Filter.Eventually.frequently (Filter.Eventually.of_forall fun _ => le_rfl))
    (fun n => ⟨worldTrue, trivialDP_consistentWith _ _⟩)
  intro n v _
  rw [buyDaily_netWorth]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [project_zeroP]
  unfold PCWorld.payout
  rw [if_pos (PCWorld.holds_top v)]
  norm_num

/-- **N− for `combo_exploits_of_exploits`**: its hypothesis package `hexp` is inhabited — on the
zero history over the empty process, by the buy-`⊤`-daily trader — and the conclusion follows: the
combined mirror exploits `zeroP`. Degenerate (a constant pricing over the empty process); the lemma
is used contrapositively inside Lemma A, where the real instance is `paperProjection_package`.
Source: audit r1 (adversarial) 3
Kind: N-
Fidelity: exact -/
theorem combo_exploits_zeroP (u : ℕ) :
    (Trader.affineCombo (1 / 2) (Trader.mirror u (fun _ => 1 / 2) true (buyDaily ⊤))
      (Trader.mirror u (fun _ => 1 / 2) false (buyDaily ⊤))).Exploits zeroP trivialDP :=
  combo_exploits_of_exploits zeroP trivialDP u (fun _ φ h => absurd h (Finset.notMem_empty φ))
    (fun _ => 1 / 2) (1 / 2) (by norm_num) (fun _ => by norm_num) 0 (fun _ _ => rfl)
    (buyDaily ⊤) (buyDaily_top_exploits_project_zeroP u _)

/-! ## T4.3 The achievable limits on a fresh atom -/

/-- **Every inductor's limiting belief on a fresh atom is interior**: in `(0,1)`. Non-dogmatism
with the both-bits-plausible premises derived from freshness (T1.2), never assumed.
Source: [[lean-deference-2-inventory]] 032(b); [[self-referential-settlement-target]] §5.3 ("non-dogmatism confines manipulation to the interior")
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem limitingBelief_atom_mem_Ioo (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (u : ℕ) (hu : AtomFreeProcess u DP) :
    limitingBelief P (Formula.atom u) ∈ Set.Ioo (0 : ℝ) 1 := by
  obtain ⟨L, hL, hL0⟩ := lic_exists_limit_pos P DP (Formula.atom u)
    (exists_consistent_holds_atom hu hworld)
  obtain ⟨L', hL', hL1⟩ := lic_exists_limit_lt_one P DP (Formula.atom u)
    (exists_consistent_not_holds_atom hu hworld)
  have h1 : limitingBelief P (Formula.atom u) = L := hL.limsup_eq
  have h2 : limitingBelief P (Formula.atom u) = L' := hL'.limsup_eq
  exact ⟨by rw [h1]; exact hL0, by rw [h2]; exact hL1⟩

/-- Limit coherence on the atom and its negation (FAF's `lic_limitingBelief_add_neg`).
Source: [[lean-deference-2-inventory]] 032(b) ("coherence pins only `P_∞(φ) + P_∞(∼φ) = 1`")
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem limitingBelief_atom_add_neg (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (u : ℕ) :
    limitingBelief P (Formula.atom u) + limitingBelief P (∼Formula.atom u) = 1 :=
  lic_limitingBelief_add_neg P DP hworld _

/-- **The achievable limits on a fresh atom, rational form.** Over `DP` with a consistent world at
every stage and `u` fresh: (⊆) every inductor's limiting belief on `u` is in `(0,1)`, and (⊇) given
any one inductor `P₀` over `DP`, every rational `c ∈ (0,1)` is the limiting belief of an inductor
over `DP` — the projection `project P₀ u (fun _ => c)`. The set is squeezed between `ℚ ∩ (0,1)` and
`(0,1)`; the irrational case is OPEN (T7.5). The (⊇) half rests on Lemma A (OPEN certificate); the
limit value itself is proved outright.
Source: [[lean-deference-2-inventory]] 032(b)–(c) (its conjecture (c), FAF-native form); [[anson-2-inventory]] 003 (limit form)
Kind: C
Fidelity: variant: rational values attained; "isolated" rendered as `AtomFreeProcess` (the propositional reading)
Hyps: (a); (⊇) rests on the OPEN rewriters -/
theorem achievable_limits_fresh_atom_rat (DP : DeductiveProcess)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (u : ℕ) (hu : AtomFreeProcess u DP)
    (P₀ : History) [IsLogicalInductor P₀ DP] :
    (∀ P : History, IsLogicalInductor P DP → limitingBelief P (Formula.atom u) ∈ Set.Ioo (0 : ℝ) 1) ∧
    (∀ c : ℚ, 0 < c → c < 1 →
      ∃ P : History, IsLogicalInductor P DP ∧ limitingBelief P (Formula.atom u) = c) :=
  ⟨fun P hP => by haveI := hP; exact limitingBelief_atom_mem_Ioo P DP hworld u hu,
   fun c hc0 hc1 => ⟨project P₀ u (fun _ => c), project_const_isLogicalInductor P₀ DP u hu c hc0 hc1,
     limitingBelief_project_const_atom P₀ DP hworld u c⟩⟩

/-! ## Jeffrey-form finite-jump manipulation -/

/-- **Jeffrey-form steering with one jump** (anson-044's finite-jump case) is Lemma A: the weight
`q₀` before day `N` and `c*` from day `N` on gives an inductor whose limiting belief on `u` is `c*`.
Source: [[anson-inventory]] 044 (the L case, finite jumps); [[dose-response]] §6.1 Lemma A
Kind: C
Fidelity: exact (one jump; the general varying-marginal form is OPEN T7.5)
Hyps: (a); rests on the OPEN rewriters through Lemma A -/
theorem jeffrey_steering_finiteJumps (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (u : ℕ) (hu : AtomFreeProcess u DP)
    (q₀ cstar η : ℚ) (hη : 0 < η) (hq₀ : η ≤ q₀ ∧ q₀ ≤ 1 - η) (hc : η ≤ cstar ∧ cstar ≤ 1 - η)
    (N : ℕ) :
    IsLogicalInductor (project P u (fun n => if n < N then q₀ else cstar)) DP ∧
    limitingBelief (project P u (fun n => if n < N then q₀ else cstar)) (Formula.atom u) = cstar := by
  have hjump : ∀ n, N ≤ n → (if n < N then q₀ else cstar) = (if N < N then q₀ else cstar) := by
    intro n hn
    rw [if_neg (not_lt.mpr hn), if_neg (lt_irrefl N)]
  refine ⟨project_isLogicalInductor P DP u hu _ η hη (fun n => ?_)
    (MachineRatCodes.ofFiniteTable _ N cstar fun n hn => by rw [if_neg (not_lt.mpr hn)]) N hjump, ?_⟩
  · split_ifs <;> assumption
  · rw [limitingBelief_project_atom P DP hworld u _ N hjump, if_neg (lt_irrefl N)]

end Cleanroom.Li.LiProjection
