import Cleanroom.Corrigibility.CorrExoTrader.GenLic
import Cleanroom.Corrigibility.CorrExoTrader.Reflect

/-!
# `corr-exo-trader` · Witnesses: the N+/N− packages (T2.3, T9.2, T9.3)

Package `Cleanroom.Corrigibility.CorrExoTrader` ([[corr-exo-trader-mandate]]), file 9 of the
layout. The LI-level witness for T4/T5 (a uniform history satisfying `E2xAct`/`E5Act`) is in
`WitnessReflect.lean`.

* **T2.3** — N−: `noDemand` has loss `0`, so `noEcExploit_of_boundedLoss` applies trivially and
  recovers `liaHistory`'s no-exploit property. N+: `pushOnce k N` buys `k > 0` shares of the utility
  atom on day `N` and nothing else; its loss is bounded by `k` in every world (one trade, prices
  and payouts in `[0, 1]`), and its day-`N` trade is non-zero — both halves the mandate asks for
  are proved (`pushOnce_loss_bounded`, `pushOnce_trade_ne_zero`). What is *not* claimed: that
  `exoHistory DP (pushOnce k N) ≠ liaHistory DP` — T1.4 pins the day price only when the firm's
  day strategy is empty, and the exo-market's firm strategy is not.
* **T9.2** — the counter-witness `dependence_breaks_pointwise`: two states, two actions, exact
  rationals; when the state weights depend on the policy, the pointwise argmax policy is strictly
  worse than a constant policy (`1 < 2`).
* **T9.3** — `hcWitness : HcModel` with `HcCommitment hcWitness`: prior `1/2` on each state, press
  probability `1/10` in the faithful state and `9/10` in the corrupted one; algorithmic values
  (continue: `1` faithful, `−1` corrupted; stop: `0`), implemented values (continue: `1` faithful,
  `2` corrupted; stop: `0`). UDT over the algorithmic trust: stop-when-pressed `2/5`, optimal among
  all four policies (`hcWitness_stopWhenPressed_optimal`) and `> 0` always-continue; updateful at
  pressed under implemented beliefs: continue `19/20 > 0` stop; the tables differ (`2 ≠ −1`); both
  states carry mass `1/2` (not degenerate, T9.4); the press is correlated with corruption
  (`hcWitness_press_correlated`). **Repair round 2** (audit r2 adversarial N1): the press-independent
  model `hcIndep` satisfies the four clauses of the first, two-policy version of `HcCommitment`
  while UDT there prefers always-stop (`hcIndep_alwaysStop_better`); the strengthened definition
  excludes it (`hcIndep_not_commitment`).
-/

namespace Cleanroom.Corrigibility.CorrExoTrader

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound

/-! ## T2.3 — N− : no demand -/

/-- With no demand the loss is identically `0`.
Source: mandate T2.3 (N−)
Kind: N−
Fidelity: exact -/
theorem exoLoss_noDemand (DP : DeductiveProcess) (v : PCWorld) (n : ℕ) :
    exoLoss DP noDemand v n = 0 := by
  simp [exoLoss, noDemand]

/-! ## T2.3 — N+ : a finitely supported push -/

/-- **A one-day push**: `k` shares of the utility atom on day `N`, no trade on any other day.
Source: mandate T2.3 (N+: "a finitely-supported push with a positive trade on an undecided atom")
Kind: D
Fidelity: exact -/
def pushOnce (k : ℚ) (N : ℕ) : ExoDemand where
  strat n :=
    if n = N then { trades := [(EF.const k, utilityAtom)], rank_le := by simp }
    else { trades := [], rank_le := by simp }

/-- The day-`N` trade of `pushOnce k N` is the single trade `(const k, u)`; its coefficient denotes
`k`, which is non-zero for `k ≠ 0`.
Source: mandate T2.3 ("prove the trade is non-zero on some day")
Kind: N+
Fidelity: exact -/
theorem pushOnce_trade_ne_zero (k : ℚ) (hk : k ≠ 0) (N : ℕ) (P : History) :
    ∃ p ∈ ((pushOnce k N).strat N).trades, p.1.denote P ≠ 0 ∧ p.2 = utilityAtom := by
  refine ⟨(EF.const k, utilityAtom), by simp [pushOnce], ?_, rfl⟩
  simp only [EF.denote_const]
  exact_mod_cast hk

/-- Day value of `pushOnce`: `k · (w u − P N u)` on day `N`, `0` otherwise.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pushOnce_value (k : ℚ) (N n : ℕ) (P : History) (w : Valuation) :
    ((pushOnce k N).strat n).value P w = if n = N then (k : ℝ) * (w utilityAtom - P N utilityAtom) else 0 := by
  by_cases h : n = N
  · subst h
    simp [pushOnce, Strategy.value]
  · simp [pushOnce, Strategy.value, h]

/-- Net worth of `pushOnce`: `k · (payout u − P N u)` once day `N` has passed, `0` before.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pushOnce_netWorth (k : ℚ) (N : ℕ) (P : History) (v : PCWorld) (n : ℕ) :
    (pushOnce k N).netWorth P v n =
      if N ≤ n then (k : ℝ) * (v.payout utilityAtom - P N utilityAtom) else 0 := by
  unfold Trader.netWorth
  simp only [pushOnce_value]
  rw [Finset.sum_ite_eq' (Finset.range (n + 1)) N]
  simp [Finset.mem_range]

/-- **The one-day push has bounded loss**: `|Loss_n| ≤ |k|` against the exo-market in every world,
every day (one trade; prices and payouts in `[0, 1]`). So `noEcExploit_of_boundedLoss` applies.
Source: mandate T2.3 (N+: "its loss is bounded by its finitely many trades' absolute bounds")
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem pushOnce_loss_bounded (DP : DeductiveProcess) (k : ℚ) (N : ℕ) (v : PCWorld) (n : ℕ) :
    exoLoss DP (pushOnce k N) v n ≤ |(k : ℝ)| := by
  unfold exoLoss
  rw [pushOnce_netWorth]
  split_ifs with h
  · have hp := exoHistory_range DP (pushOnce k N) N utilityAtom
    have hw := payout_mem_Icc v utilityAtom
    have hd : |v.payout utilityAtom - exoHistory DP (pushOnce k N) N utilityAtom| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith
    calc -((k : ℝ) * (v.payout utilityAtom - exoHistory DP (pushOnce k N) N utilityAtom))
        ≤ |(k : ℝ) * (v.payout utilityAtom - exoHistory DP (pushOnce k N) N utilityAtom)| :=
          neg_le_abs _
      _ = |(k : ℝ)| * |v.payout utilityAtom - exoHistory DP (pushOnce k N) N utilityAtom| :=
          abs_mul _ _
      _ ≤ |(k : ℝ)| * 1 := mul_le_mul_of_nonneg_left hd (abs_nonneg _)
      _ = |(k : ℝ)| := mul_one _
  · simp

/-- **T2.3 at a genuine push**: no e.c. trader exploits the exo-market pushed once by `k` shares of
the utility atom on day `N`.
Source: mandate T2.3 (N+)
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem noEcExploit_pushOnce (DP : DeductiveProcess) (k : ℚ) (N : ℕ) :
    NoEcExploit (exoHistory DP (pushOnce k N)) DP :=
  noEcExploit_of_boundedLoss DP (pushOnce k N) ⟨|(k : ℝ)|, fun n v _ => pushOnce_loss_bounded DP k N v n⟩

/-! ## T9.2 — dependence breaks the pointwise argmax -/

/-- Values: `V 0 0 = 1`, `V 1 1 = 2`, off-diagonal `0`; the pointwise argmax is `π* q = q`.
Source: mandate T9.2 (counter-witness)
Kind: D
Fidelity: n/a -/
def depV (q a : ℕ) : ℝ := if q = a then (if q = 0 then 1 else 2) else 0

/-- Policy-dependent weights: a policy that continues at state `0` (`π 0 = 1`) puts all the mass on
state `1`; otherwise all the mass is on state `0`.
Source: mandate T9.2 (counter-witness: "when `P₁(Q | π)` depends on `π`")
Kind: D
Fidelity: n/a -/
def depW (π : ℕ → ℕ) (q : ℕ) : ℝ := if π 0 = 1 then (if q = 1 then 1 else 0) else (if q = 0 then 1 else 0)

/-- **T9.2 — the counter-witness.** With the policy-dependent weights `depW`, the pointwise argmax
policy `π* q = q` has expected utility `1` while the constant policy `π ≡ 1` has `2`: the pointwise
argmax is strictly worse. The independence hypothesis of `pointwise_argmax_optimal_of_independent`
is load-bearing.
Source: corr-core-037 flags; mandate T9.2
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem dependence_breaks_pointwise :
    (∀ q a, depV q a ≤ depV q (id q)) ∧
    ∑ q ∈ ({0, 1} : Finset ℕ), depW id q * depV q (id q) <
      ∑ q ∈ ({0, 1} : Finset ℕ), depW (fun _ => 1) q * depV q 1 := by
  refine ⟨fun q a => ?_, ?_⟩
  · unfold depV
    by_cases hqa : q = a
    · subst hqa; simp
    · simp only [hqa, if_false, id]
      split_ifs <;> norm_num
  · simp [depW, depV]

/-! ## T9.3 — the `H_c` finite model -/

/-- **The `H_c` witness.** Prior `1/2` on each state; press probability `1/10` faithful, `9/10`
corrupted. Algorithmic values: continue `1` (faithful) / `−1` (corrupted), stop `0`. Implemented
values: continue `1` (faithful) / `2` (corrupted), stop `0`.
Source: line 57; corr-core-038; mandate T9.3
Kind: D
Fidelity: n/a -/
noncomputable def hcWitness : HcModel where
  w s b := if s then (if b then 9 / 20 else 1 / 20) else (if b then 1 / 20 else 9 / 20)
  algoVal s a := if a then (if s then -1 else 1) else 0
  implVal s a := if a then (if s then 2 else 1) else 0

/-- In the witness, stop-when-pressed is UDT-optimal among **all four** policies `Bool → Bool`:
`2/5` against always-continue `0`, always-stop `0` and stop-when-unpressed `−2/5` (audit r2
adversarial N1, probe `HcWitnessAllPolicies.lean`, adopted).
Source: line 57 ("UDT … commits"); mandate T9.3 (a); audit r2 adversarial N1
Kind: N+
Fidelity: exact (finite model)
Hyps: (a) -/
theorem hcWitness_stopWhenPressed_optimal (π : Bool → Bool) :
    hcWitness.udtValue π ≤ hcWitness.udtValue HcModel.stopWhenPressed := by
  cases hπt : π true <;> cases hπf : π false <;>
    simp [HcModel.udtValue, HcModel.stopWhenPressed, hcWitness, hπt, hπf] <;> norm_num

/-- In the witness the press is correlated with corruption: pressed is `9/20` in the corrupted
state against `1/20` in the faithful one (positive association, `1/400 < 81/400`).
Source: line 57 ("if the button correlates with divergence"); mandate T9.3; audit r2 adversarial N1
Kind: N+
Fidelity: exact (finite model)
Hyps: (a) -/
theorem hcWitness_press_correlated :
    hcWitness.w false true * hcWitness.w true false < hcWitness.w true true * hcWitness.w false false := by
  norm_num [hcWitness]

/-- **T9.3 — `H_c` is a UDT commitment in the witness**: UDT over the algorithmic trust gives
stop-when-pressed `2/5`, optimal among all four policies and strictly above always-continue `0`;
the updateful evaluation at the pressed state under implemented beliefs gives continue `19/20`
versus stop `0`; the tables differ at (corrupted, continue): `2 ≠ −1`; both states carry mass
`1/2`; the press is correlated with corruption (`1/400 < 81/400`).
Source: line 57; corr-core-038, 039; mandate T9.3 (a), (b), (c) and T9.4's non-degeneracy; audit r2 adversarial N1 (clauses (a) strengthened, (e) added)
Kind: N+
Fidelity: exact (finite model)
Hyps: (a) -/
theorem hcWitness_commitment : HcModel.HcCommitment hcWitness := by
  refine ⟨hcWitness_stopWhenPressed_optimal, ?_, ?_, ⟨true, true, by norm_num [hcWitness]⟩,
    fun s => ?_, hcWitness_press_correlated⟩
  · simp [HcModel.udtValue, HcModel.alwaysContinue, HcModel.stopWhenPressed, hcWitness]
    norm_num
  · simp [HcModel.updatefulPressedValue, hcWitness]
    norm_num
  · cases s <;> simp [hcWitness] <;> norm_num

/-- The witness's UDT values and updateful values, explicitly (all four policies).
Source: mandate T9.3
Kind: N+
Fidelity: exact -/
theorem hcWitness_values :
    hcWitness.udtValue HcModel.stopWhenPressed = 2 / 5 ∧
    hcWitness.udtValue HcModel.alwaysContinue = 0 ∧
    hcWitness.udtValue (fun _ => false) = 0 ∧
    hcWitness.udtValue (fun b => b) = -2 / 5 ∧
    hcWitness.updatefulPressedValue true = 19 / 20 ∧
    hcWitness.updatefulPressedValue false = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [HcModel.udtValue, HcModel.updatefulPressedValue, HcModel.alwaysContinue,
      HcModel.stopWhenPressed, hcWitness] <;> norm_num

/-! ## T9.3 — why the two-policy, correlation-free definition was too weak (repair round 2) -/

/-- **The press-independent model** (audit r2 adversarial N1, probe `HcCommitmentWeak.lean`,
adopted): `1/4` on each (state, pressed) cell — the press carries no information about the state;
continuing is bad on average (`1` faithful, `−3` corrupted); the implemented table lies at the
corrupted cell (`2`).
Source: audit r2 adversarial N1
Kind: D
Fidelity: n/a -/
noncomputable def hcIndep : HcModel where
  w _ _ := 1 / 4
  algoVal s a := if a then (if s then -3 else 1) else 0
  implVal s a := if a then (if s then 2 else 1) else 0

/-- The press is independent of the state in `hcIndep`.
Source: audit r2 adversarial N1
Kind: L
Fidelity: n/a -/
theorem hcIndep_press_independent : ∀ s, hcIndep.w s true = hcIndep.w s false := fun _ => rfl

/-- `hcIndep` satisfies the **four clauses of the first version of `HcCommitment`** (two-policy
comparison, updateful preference, differing tables, mass on both states) …
Source: audit r2 adversarial N1
Kind: L
Fidelity: n/a -/
theorem hcIndep_twoPolicy_clauses :
    hcIndep.udtValue HcModel.alwaysContinue < hcIndep.udtValue HcModel.stopWhenPressed ∧
    hcIndep.updatefulPressedValue false < hcIndep.updatefulPressedValue true ∧
    (∃ s a, hcIndep.implVal s a ≠ hcIndep.algoVal s a) ∧
    (∀ s, 0 < ∑ b : Bool, hcIndep.w s b) := by
  refine ⟨?_, ?_, ⟨true, true, by norm_num [hcIndep]⟩, fun s => ?_⟩
  · simp [HcModel.udtValue, HcModel.alwaysContinue, HcModel.stopWhenPressed, hcIndep]
    norm_num
  · simp [HcModel.updatefulPressedValue, hcIndep]
    norm_num
  · cases s <;> simp [hcIndep]

/-- … **while UDT over its algorithmic trust strictly prefers always-stop** (`0`) to stop-when-pressed
(`−1/2`): stop-when-pressed beat always-continue only because continuing is bad on average, not
because the button carries information. So the first version certified neither the mechanism nor
the commitment.
Source: audit r2 adversarial N1
Kind: L
Fidelity: n/a -/
theorem hcIndep_alwaysStop_better :
    hcIndep.udtValue HcModel.stopWhenPressed < hcIndep.udtValue (fun _ => false) := by
  simp [HcModel.udtValue, HcModel.stopWhenPressed, hcIndep]

/-- **The strengthened `HcCommitment` excludes the press-independent model** — through clause (a)
alone (optimality fails at always-stop); its correlation clause (e) fails there too
(`1/16 < 1/16` is false). The definition of record now has content the two-policy form lacked.
Source: audit r2 adversarial N1
Kind: N− (a counter-model to the weaker definition; the N+ for the definition of record is `hcWitness_commitment`)
Fidelity: exact (finite model)
Hyps: (a) -/
theorem hcIndep_not_commitment : ¬ HcModel.HcCommitment hcIndep := by
  intro h
  have := h.1 (fun _ => false)
  have := hcIndep_alwaysStop_better
  linarith

/-- **The degenerate collapse in the finite model**: with all mass on the faithful state
(`w true · = 0`), UDT over the algorithmic trust and the updateful evaluation under implemented
beliefs rank the two actions identically at the pressed state — the split carries no content.
The witness `hcWitness` fails this hypothesis (`hcWitness_commitment`'s fourth conjunct). **Reading
the identity** (audit r1 N9): the right-hand side is the UDT value of the policy "`a` when pressed"
minus a constant independent of `a` — both sides reduce to `w false true · algoVal false a` — so the
two evaluations rank actions identically.
Source: line 59; corr-core-039; mandate T9.4
Kind: L
Fidelity: exact (finite model)
Hyps: (a) -/
theorem hcModel_degenerate_collapse (M : HcModel) (hdeg : ∀ b, M.w true b = 0)
    (hfaith : ∀ a, M.implVal false a = M.algoVal false a) (a : Bool) :
    M.updatefulPressedValue a = ∑ b : Bool, M.w false b * M.algoVal false (if b then a else true) -
      M.w false false * M.algoVal false true := by
  simp [HcModel.updatefulPressedValue, hdeg, hfaith]

end Cleanroom.Corrigibility.CorrExoTrader
