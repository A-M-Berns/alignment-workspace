import Cleanroom.Bli.BliTransfer.AttemptB.Transfer
import LogicalInduction.Framework.Machine.SpliceMachine

/-!
# `bli-transfer` · attempt B · Clamp: T3 refuted — the clamped market is never a logical
inductor, and e.c. trade magnitude is not `2^{poly}`

**The claim under test (T3, [[bli-program]] §3.2(d), L5; bli-paper-033/039, bli-slides-006/008,
bli-soto-a-002 reading C).** `IsLogicalInductor Q DP → IsLogicalInductor (clamp Q) DP`, where
`clamp Q k ψ = max (min (Q k ψ) (1 − ε_k)) ε_k` with `ε_k = 2^{-2^k}`, via a rewrite (exact on
the coefficients) plus a settlement residual `≤ magnitude · ε_n`, summable because "trade
magnitude `≤ 2^{p(n)}`" (§4 L5, mandate Known issue 7).

**Both are false.** FAF's expressible features have `letE` sharing, so `j` nested squarings of
`const 2` — cost `O(j)`, token stream `O(j)` — denote `2^{2^j}` (`sqTower_denoteWith`). The
trader `sellBottom` sells `2^{2^{n+1}}` shares of `⊥` on day `n`; it is efficiently computable
(`sellBottom_ec`, machine data through `concatVar`), its magnitude is `2^{2^{n+1}}`
(`sellBottom_magnitude`), which beats `2^{p(n)}` for every polynomial `p`
(`not_magnitude_le_two_pow_poly`: Known issue 7's bound refuted), and on **any** market
that prices `⊥` at `≥ ε_n` it banks `≥ 2^{2^{n+1}} · 2^{-2^n} = 2^{2^n}` per day with no downside
(`⊥` pays `0` in every world): `sellBottom_exploits`. The clamp forces exactly this
(`clamp_mem_Icc`), so `clamp Q` is exploited for **every** history `Q` — an inductor or not —
over every deductive process with consistent worlds (`clamp_not_isLogicalInductor`). The
non-vacuity guard is `hworld` (trap (v)); at `paperDP 𝗜𝚺₁` it is FAF's `paperDP_hworld`
(`WitnessLia.lean`).

**What this says about the sources.** Any re-pricing that forces a positive floor
`δ_n ≥ 2^{-2^{p(n)}}` on a refuted sentence is exploitable by the same trader; since an e.c.
trader's coefficients are bounded by `2^{2^{poly}}` (the true bound; not proved here) and an
expressible floor is bounded below by the same kind of quantity, *no* clamp rate rescues the
clamped variant. Route A's rounding (T4) escapes this attack only if it rounds a refuted
sentence's price *down* (the findings file records the analysis).

Sources: [[bli-program]] §3.2(d), §4 L5; mandate T3, Known issue 7.
-/

namespace Cleanroom.Bli.BliTransfer.AttemptB

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound

/-! ## `ε_k` and the clamp's range -/

/-- `0 < ε_k`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma epsK_pos (k : ℕ) : 0 < epsK k := by unfold epsK; positivity

/-- `ε_k ≤ 1/2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma epsK_le_half (k : ℕ) : epsK k ≤ 1 / 2 := by
  unfold epsK
  calc (1 / 2 : ℚ) ^ (2 ^ k) ≤ (1 / 2 : ℚ) ^ 1 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) Nat.one_le_two_pow
    _ = 1 / 2 := pow_one _

/-- **The clamp's range**: every clamped price lies in `[ε_k, 1 − ε_k]` — the non-dogmatism
fact `bli-assemble` wanted to transport, and exactly the floor `sellBottom` exploits.
Source: mandate T3 (`clamp_mem_Ioo`)
Kind: L
Fidelity: exact -/
lemma clamp_mem_Icc (Q : History) (k : ℕ) (φ : Sentence) :
    (epsK k : ℝ) ≤ clamp Q k φ ∧ clamp Q k φ ≤ 1 - (epsK k : ℝ) := by
  have h : ((epsK k : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := by exact_mod_cast epsK_le_half k
  push_cast at h
  unfold clamp
  constructor
  · exact le_max_right _ _
  · apply max_le
    · exact min_le_right _ _
    · linarith

/-! ## The squaring tower -/

/-- `sqTower j`: `j` nested `letE`-squarings of `const 2`, denoting `2^{2^j}` at cost `O(j)`.
Source: mandate T3 (refutation of Known issue 7)
Kind: D
Fidelity: n/a -/
def sqTower : ℕ → LogicalInduction.EF
  | 0 => .const 2
  | j + 1 => .letE (sqTower j) (.mul (.var 0) (.var 0))

/-- `sqTower j` denotes `2^{2^j}` in every environment against every market.
Source: none: infrastructure
Kind: P
Fidelity: n/a -/
lemma sqTower_denoteWith (V : History) : ∀ (j : ℕ) (ρ : List ℝ),
    (sqTower j).denoteWith ρ V = (2 : ℝ) ^ (2 ^ j) := by
  intro j
  induction j with
  | zero => intro ρ; simp [sqTower]
  | succ j ih =>
      intro ρ
      simp only [sqTower, LogicalInduction.EF.denoteWith_letE, LogicalInduction.EF.denoteWith_mul,
        LogicalInduction.EF.denoteWith_var, List.getD_cons_zero, ih ρ]
      rw [pow_succ, pow_mul, sq]

/-- `sqTower j` has rank `0` (no price leaves).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sqTower_rank : ∀ j, (sqTower j).rank = 0
  | 0 => rfl
  | j + 1 => by simp [sqTower, sqTower_rank j]

/-- `sqTower j` is price-free.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sqTower_priceFree : ∀ j, (sqTower j).priceFree
  | 0 => trivial
  | j + 1 => ⟨sqTower_priceFree j, trivial, trivial⟩

/-- The token stream of `sqTower j`: the constant `2` then `j` copies of the squaring block.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sqTower_serialize : ∀ j, (sqTower j).serialize =
    [1, Encodable.encode (2 : ℚ)] ++ (List.range j).flatMap (fun _ => [7, 0, 7, 0, 3, 8])
  | 0 => by simp [sqTower, LogicalInduction.EF.serialize]
  | j + 1 => by
      simp only [sqTower, LogicalInduction.EF.serialize, sqTower_serialize j, List.range_succ,
        List.flatMap_append, List.flatMap_singleton, List.append_assoc]
      rfl

/-! ## The trader -/

/-- The day-`n` coefficient: `−2^{2^{n+1}}`.
Source: mandate T3 (refutation)
Kind: D
Fidelity: n/a -/
def sellBottomCoeff (n : ℕ) : LogicalInduction.EF := .mul (.const (-1)) (sqTower (n + 1))

/-- The day-`n` coefficient denotes `−2^{2^{n+1}}`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sellBottomCoeff_denote (V : History) (n : ℕ) :
    (sellBottomCoeff n).denote V = -((2 : ℝ) ^ (2 ^ (n + 1))) := by
  simp [sellBottomCoeff, LogicalInduction.EF.denote, sqTower_denoteWith]

/-- **The `⊥`-seller**: on day `n`, sell `2^{2^{n+1}}` shares of `⊥`.
Source: mandate T3 (refutation)
Kind: D
Fidelity: n/a -/
def sellBottom : Trader where
  strat n := { trades := [(sellBottomCoeff n, ⊥)], rank_le := by simp [sellBottomCoeff, sqTower_rank] }

/-- `⊥` pays `0` in every p.c. world.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma payout_falsum (v : PCWorld) : v.payout ⊥ = 0 := by
  simp [PCWorld.payout, PCWorld.Holds, LO.Propositional.Formula.Boolean.val]

/-- The day-`n` value of the `⊥`-seller in any world: `2^{2^{n+1}} · P n ⊥`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sellBottom_value (P : History) (v : PCWorld) (n : ℕ) :
    (sellBottom.strat n).value P v.payout = (2 : ℝ) ^ (2 ^ (n + 1)) * P n ⊥ := by
  simp [sellBottom, LogicalInduction.Strategy.value, sellBottomCoeff_denote, payout_falsum]

/-- The `⊥`-seller's magnitude is `2^{2^{n+1}}` against every market.
Source: mandate T3 (refutation of Known issue 7)
Kind: L
Fidelity: n/a -/
lemma sellBottom_magnitude (V : History) (n : ℕ) :
    (sellBottom.strat n).magnitude V = (2 : ℝ) ^ (2 ^ (n + 1)) := by
  simp [sellBottom, LogicalInduction.Strategy.magnitude, sellBottomCoeff_denote]

/-- **The `⊥`-seller is efficiently computable**: one trade per day, the constant sentence `⊥`,
and a price-free coefficient stream `[1, ⌜−1⌝, 1, ⌜2⌝] ++ (n+1) × [7,0,7,0,3,8] ++ [3]`
emitted by `MachineTokenStream.concatVar` at the ruler `n + 1`.
Source: mandate T3 (refutation)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem sellBottom_ec : EfficientlyComputable sellBottom := by
  have hstream : MachineTokenStream (fun z => (sellBottomCoeff z.unpair.1).serialize) := by
    refine (((MachineTokenStream.const [1, Encodable.encode (-1 : ℚ), 1, Encodable.encode (2 : ℚ)]).append
      ((MachineTokenStream.const [7, 0, 7, 0, 3, 8]).concatVar UnaryRuler.unpairFst.succ)).append
      (MachineTokenStream.const [3])).of_eq (fun z => ?_)
    simp [sellBottomCoeff, LogicalInduction.EF.serialize, sqTower_serialize]
  refine EfficientlyComputable.ofTradeBlocksBig sellBottom (fun _ => 1)
    (fun z => sellBottomCoeff z.unpair.1) (fun _ => ⊥) (UnaryRuler.const 1)
    (MachineSpliceStream.ofPriceFree hstream (fun z => ⟨trivial, sqTower_priceFree _⟩))
    (MachineSentenceCodes.const ⊥) (fun n => by simp [sellBottom, Nat.unpair_pair])

/-! ## The exploitation -/

/-- **Any market pricing `⊥` at `≥ ε_n` (and `≥ 0`) is exploited by the `⊥`-seller**, over any
process with consistent worlds: net worth is `≥ 0` in every world and `≥ 2^{2^n}` on day `n`.
Source: mandate T3 (refutation); [[bli-program]] §3.2(d)
Kind: P
Fidelity: stronger: any market with the floor, not only the clamp
Hyps: (a) -/
theorem sellBottom_exploits (P : History) (DP : DeductiveProcess)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hP0 : ∀ n, 0 ≤ P n ⊥) (hP : ∀ n, (epsK n : ℝ) ≤ P n ⊥) :
    sellBottom.Exploits P DP := by
  have hnw : ∀ v n, sellBottom.netWorth P v n =
      ∑ i ∈ Finset.range (n + 1), (2 : ℝ) ^ (2 ^ (i + 1)) * P i ⊥ := by
    intro v n
    simp only [Trader.netWorth, sellBottom_value]
  have hnonneg : ∀ v n, 0 ≤ sellBottom.netWorth P v n := by
    intro v n
    rw [hnw]
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (by positivity) (hP0 i))
  have hbig : ∀ v n, (2 : ℝ) ^ (2 ^ n) ≤ sellBottom.netWorth P v n := by
    intro v n
    rw [hnw]
    have hterm : (2 : ℝ) ^ (2 ^ n) ≤ (2 : ℝ) ^ (2 ^ (n + 1)) * P n ⊥ := by
      have heps : ((epsK n : ℚ) : ℝ) = ((2 : ℝ) ^ (2 ^ n))⁻¹ := by
        simp [epsK, one_div, inv_pow]
      have h2 : (2 : ℝ) ^ (2 ^ (n + 1)) = (2 : ℝ) ^ (2 ^ n) * (2 : ℝ) ^ (2 ^ n) := by
        rw [pow_succ, pow_mul, sq]
      calc (2 : ℝ) ^ (2 ^ n) = (2 : ℝ) ^ (2 ^ (n + 1)) * ((2 : ℝ) ^ (2 ^ n))⁻¹ := by
            rw [h2]; field_simp
        _ ≤ (2 : ℝ) ^ (2 ^ (n + 1)) * P n ⊥ := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            rw [← heps]; exact hP n
    calc (2 : ℝ) ^ (2 ^ n) ≤ (2 : ℝ) ^ (2 ^ (n + 1)) * P n ⊥ := hterm
      _ ≤ ∑ i ∈ Finset.range (n + 1), (2 : ℝ) ^ (2 ^ (i + 1)) * P i ⊥ :=
          Finset.single_le_sum (f := fun i => (2 : ℝ) ^ (2 ^ (i + 1)) * P i ⊥)
            (fun i _ => mul_nonneg (by positivity) (hP0 i)) (Finset.self_mem_range_succ n)
  refine ⟨⟨0, ?_⟩, ?_⟩
  · rintro x ⟨n, v, -, rfl⟩
    exact hnonneg v n
  · rintro ⟨M, hM⟩
    obtain ⟨m, hm⟩ := exists_nat_gt M
    obtain ⟨v, hv⟩ := hworld m
    have hx := hM ⟨m, v, hv, rfl⟩
    have h1 : (m : ℝ) ≤ (2 : ℝ) ^ (2 ^ m) := by
      have : m ≤ 2 ^ (2 ^ m) :=
        le_trans Nat.lt_two_pow_self.le (Nat.pow_le_pow_right (by norm_num) Nat.lt_two_pow_self.le)
      exact_mod_cast this
    linarith [hbig v m]

/-- **T3 refuted**: the clamped market is exploited by an e.c. trader for **every** history `Q`
over every process with consistent worlds, so it is never a logical inductor. Scope: the clamp
is applied to every sentence with `ε_k = 2^{-2^k}` (the definition of record); the refutation
needs neither `IsLogicalInductor Q DP` nor any property of `Q`.
Source: [[bli-program]] §3.2(d); bli-paper-033/039; bli-slides-006/008; mandate T3
Kind: P
Fidelity: n/a (refutation)
Hyps: (a) `hworld` — trap (v); at `paperDP 𝗜𝚺₁` it is `paperDP_hworld` -/
theorem clamp_not_isLogicalInductor (Q : History) (DP : DeductiveProcess)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ¬ IsLogicalInductor (clamp Q) DP := by
  intro hLI
  exact hLI.noExploit sellBottom sellBottom_ec
    (sellBottom_exploits (clamp Q) DP hworld
      (fun n => le_trans (by exact_mod_cast (epsK_pos n).le) (clamp_mem_Icc Q n ⊥).1)
      (fun n => (clamp_mem_Icc Q n ⊥).1))

/-- **Known issue 7 refuted**: no polynomial `p` bounds the `⊥`-seller's magnitude by
`2^{p(n)}` — against any market. The mandate's `magnitude_le_of_ec` is false; the true bound
is doubly exponential.
Source: [[bli-program]] §4 L5; mandate T3, Known issue 7
Kind: P
Fidelity: n/a (refutation)
Hyps: (a) -/
theorem not_magnitude_le_two_pow_poly (V : History) :
    ¬ ∃ p : Polynomial ℕ, ∀ n, (sellBottom.strat n).magnitude V ≤ (2 : ℝ) ^ p.eval n := by
  rintro ⟨p, hp⟩
  obtain ⟨N, hN⟩ := eventually_poly_le_two_pow
    (∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i) p.natDegree
  have h1 := hp N
  rw [sellBottom_magnitude] at h1
  have h2 : 2 ^ (N + 1) ≤ p.eval N :=
    (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp h1
  have h3 := polynomial_eval_le p N
  have h4 := hN N le_rfl
  have h5 : 2 ^ N < 2 ^ (N + 1) := Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self N)
  omega

end Cleanroom.Bli.BliTransfer.AttemptB
