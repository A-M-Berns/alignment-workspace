import Cleanroom.Bli.BliLinkage.AttemptA.Forced
import LogicalInduction.Framework.Machine.SpliceMachine
import LogicalInduction.Properties.Support.Exploitation

/-!
# `bli-linkage`, attempt A — K3: no degenerate linked BLI over a base whose rounded prices move

**K3a (finite half).** Under `PCPσ ∧ E5σ ∧ E1x Q P ∧ Degenerate (stateOf C) S P deg` the base must
price, on every pinned coordinate, the literal of today's cell (the entry of `deg n`) at `1` and
every other cell literal at `0` (`degenerate_lit_zero`, `degenerate_lit_one`), hence the move
sentence `∼ lit (n+1) c (today)` at `0` once it is small (`degenerate_move_zero`): K1 with all the
mass on `deg n`.

**K3b (trader half, abstract).** The buy-one trader on an e.c. family `ψ` priced at most `ε n`
on day `n` with bounded partial price sums (in particular `Summable ε`), whose sentences enter a
stage of `DP` on infinitely many days (`hdec` + `hmove`), exploits `Q` relative to `DP`
(`buyOne_exploits`) by `exploits_of_bddBelow_of_unbounded`: bounded below by `−C` (long
positions, payouts `≥ 0`), unbounded above because any `N` moved days have all entered by some
stage and every world consistent with it pays them. `buyOne_efficientlyComputable` certifies
the trader through `EfficientlyComputable.ofSingleTradeBlocksBig` with the constant feature
stream. The "moves" hypothesis `hmove` is explicit — the mandate's § K3 says why it cannot be
derived from the criterion (the program's `lic_provind` reading is a misreading; findings).

**Conclusion of record** (`no_degenerate_linked_bli`): over a logical inductor `Q` with the
move sentences of a B2-shaped `(C, index, χ)` e.c. and eventually pinned, and moving infinitely
often (as entry into a stage), no `P` satisfies `PCPσ ∧ E5σ ∧ E1x Q P ∧ Degenerate`.
-/

namespace Cleanroom.Bli.BliLinkage.AttemptA

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound Cleanroom.Bli.BliTrajectory

open Classical

variable {DP : DeductiveProcess}

/-! ## Two consequences of coherence used below -/

/-- A coherent price is nonnegative on the algebra.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma nonneg_of_coherentOnCell (C : CellFamily DP) {D : Finset Sentence} {m : ℕ} {A : Finset ℕ}
    {p : Sentence → ℝ} (h : CoherentOnCell C D m A p) {φ : Sentence}
    (hφ : sentenceAtomCodes φ ⊆ A) : 0 ≤ p φ := by
  obtain ⟨k, W, w, -, hw, -, hrep⟩ := h
  rw [hrep φ hφ]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (payout_mem_Icc _ _).1

/-- A coherent price of a negation is one minus the price, on the algebra.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma neg_of_coherentOnCell (C : CellFamily DP) {D : Finset Sentence} {m : ℕ} {A : Finset ℕ}
    {p : Sentence → ℝ} (h : CoherentOnCell C D m A p) {φ : Sentence}
    (hφ : sentenceAtomCodes φ ⊆ A) : p (∼ φ) = 1 - p φ := by
  obtain ⟨k, W, w, -, -, hsum, hrep⟩ := h
  rw [hrep φ hφ, hrep (∼ φ) (by rwa [sentenceAtomCodes_neg])]
  have : ∀ i, w i * (W i).payout (∼ φ) = w i - w i * (W i).payout φ := by
    intro i
    have e : (W i).payout φ + (W i).payout (∼ φ) = 1 := by
      unfold PCWorld.payout; by_cases hv : (W i).Holds φ <;> simp [hv]
    linear_combination w i * e
  rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_sub_distrib, hsum]

/-! ## K3a -/

/-- **K3a — the degenerate superbelief forces the base to price every non-today cell literal
at `0`**: with all of day `n`'s mass on `deg n`, the marginal `cellMass … c r` of a cell `r`
other than `deg n`'s entry at `c` is `0`, and K1 makes it the base's price of the literal.
Source: [[bli-program]] §3.6(iii); desiderata I2; bli-paper-043; mandate § K3 (K3a)
Kind: C
Fidelity: exact (pinned coordinates)
Hyps: (a); `hdegmem : deg n ∈ S.states (n+1)` (the degenerate table is a candidate) -/
theorem degenerate_lit_zero (C : CellFamily DP) (index : ℕ → List ℕ) (S : StateSystem)
    (Q P : History) (hT : Tabular C index S) (hcoh : PCPσ C (stateOf C) S P)
    (hE5 : E5σ (stateOf C) S P) (hE1 : E1x Q P) (deg : ℕ → ℕ)
    (hdeg : Degenerate (stateOf C) S P deg) (n : ℕ) (hdegmem : deg n ∈ S.states (n + 1))
    {c : ℕ} (hc : c ∈ pinned C index n) {r : ℕ} (hr : r ∈ C.cells (n + 1))
    (hne : entryOf c (tableOfCode (deg n)) ≠ some r) :
    Q n (C.cellLit (n + 1) c r) = 0 := by
  rw [forced_marginal_base C index S Q P hT hcoh hE5 hE1 n hc hr]
  -- every state other than `deg n` has mass zero
  have hnn : ∀ q ∈ S.states (n + 1), 0 ≤ P n (stateOf C (n + 1) q) := fun q hq =>
    nonneg_of_coherentOnCell C (hcoh n) ((atoms_subset_stateAtomsσ hq).trans Finset.subset_union_right)
  have hzero : ∀ q ∈ S.states (n + 1), q ≠ deg n → P n (stateOf C (n + 1) q) = 0 := by
    intro q hq hqne
    have hmass := (hE5 n).1
    rw [← Finset.add_sum_erase _ _ hdegmem, hdeg n] at hmass
    have hrest : ∑ q ∈ (S.states (n + 1)).erase (deg n), P n (stateOf C (n + 1) q) = 0 := by
      linarith
    exact (Finset.sum_eq_zero_iff_of_nonneg fun q hq => hnn q (Finset.mem_of_mem_erase hq)).1
      hrest q (Finset.mem_erase.2 ⟨hqne, hq⟩)
  unfold cellMass
  apply Finset.sum_eq_zero
  intro q hq
  rw [Finset.mem_filter] at hq
  exact hzero q hq.1 (fun h => hne (h ▸ hq.2))

/-- **K3a — the degenerate superbelief forces the base to price today's cell literal at `1`.**
Source: [[bli-program]] §3.6(iii); mandate § K3 (K3a)
Kind: C
Fidelity: exact (pinned coordinates)
Hyps: (a) -/
theorem degenerate_lit_one (C : CellFamily DP) (index : ℕ → List ℕ) (S : StateSystem)
    (Q P : History) (hT : Tabular C index S) (hcoh : PCPσ C (stateOf C) S P)
    (hE5 : E5σ (stateOf C) S P) (hE1 : E1x Q P) (deg : ℕ → ℕ)
    (hdeg : Degenerate (stateOf C) S P deg) (n : ℕ) (hdegmem : deg n ∈ S.states (n + 1))
    {c : ℕ} (hc : c ∈ pinned C index n) {r : ℕ} (hr : r ∈ C.cells (n + 1))
    (he : entryOf c (tableOfCode (deg n)) = some r) :
    Q n (C.cellLit (n + 1) c r) = 1 := by
  rw [forced_marginal_base C index S Q P hT hcoh hE5 hE1 n hc hr]
  have hnn : ∀ q ∈ S.states (n + 1), 0 ≤ P n (stateOf C (n + 1) q) := fun q hq =>
    nonneg_of_coherentOnCell C (hcoh n) ((atoms_subset_stateAtomsσ hq).trans Finset.subset_union_right)
  have hmass := (hE5 n).1
  have hmem : deg n ∈ (S.states (n + 1)).filter (fun q => entryOf c (tableOfCode q) = some r) :=
    Finset.mem_filter.2 ⟨hdegmem, he⟩
  have hle : ∑ q ∈ (S.states (n + 1)).filter (fun q => entryOf c (tableOfCode q) = some r),
      P n (stateOf C (n + 1) q) ≤ 1 := by
    rw [← hmass]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun q hq _ => hnn q hq)
  have hge : P n (stateOf C (n + 1) (deg n)) ≤
      ∑ q ∈ (S.states (n + 1)).filter (fun q => entryOf c (tableOfCode q) = some r),
        P n (stateOf C (n + 1) q) :=
    Finset.single_le_sum (fun q hq => hnn q (Finset.mem_filter.1 hq).1) hmem
  rw [hdeg n] at hge
  unfold cellMass
  linarith

/-- **K3a — the move sentence is priced at `0`**: `∼ lit (n+1) c (today)` has price `0` under
the base whenever it is small on day `n` (coherence gives `P (∼lit) = 1 − P lit`, `E1x`
transfers it).
Source: [[bli-program]] §3.6(iii) ("the base prices 'my price will move' at `0`"); mandate § K3
Kind: C
Fidelity: exact
Hyps: (a); `hsmall` (the negated literal small on day `n` — a slightly stronger smallness than
`pinned`'s) -/
theorem degenerate_move_zero (C : CellFamily DP) (index : ℕ → List ℕ) (S : StateSystem)
    (Q P : History) (hT : Tabular C index S) (hcoh : PCPσ C (stateOf C) S P)
    (hE5 : E5σ (stateOf C) S P) (hE1 : E1x Q P) (deg : ℕ → ℕ)
    (hdeg : Degenerate (stateOf C) S P deg) (n : ℕ) (hdegmem : deg n ∈ S.states (n + 1))
    {c : ℕ} (hc : c ∈ pinned C index n) {r : ℕ} (hr : r ∈ C.cells (n + 1))
    (he : entryOf c (tableOfCode (deg n)) = some r)
    (hsmall : (∼ C.cellLit (n + 1) c r) ∈ smallSet n) :
    Q n (∼ C.cellLit (n + 1) c r) = 0 := by
  rw [← hE1 n _ hsmall]
  rw [neg_of_coherentOnCell C (hcoh n)
    ((atoms_subset_smallAtoms (lit_mem_smallSet_of_mem_pinned hc hr)).trans Finset.subset_union_left)]
  rw [hE1 n _ (lit_mem_smallSet_of_mem_pinned hc hr),
    degenerate_lit_one C index S Q P hT hcoh hE5 hE1 deg hdeg n hdegmem hc hr he]
  ring

/-! ## K3b: the buy-one trader -/

/-- **The buy-one trader**: one share of `ψ n` on day `n`, coefficient the constant feature `1`.
Source: mandate § K3 (K3b: `buyOne ψ`)
Kind: D
Fidelity: exact -/
noncomputable def buyOne (ψ : ℕ → Sentence) : Trader where
  strat n := ⟨[(EF.const 1, ψ n)], by
    intro p hp
    simp only [List.mem_singleton] at hp
    subst hp
    simp [EF.rank_const]⟩

/-- The buy-one trader's day-`n` trade list.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma buyOne_trades (ψ : ℕ → Sentence) (n : ℕ) :
    ((buyOne ψ).strat n).trades = [(EF.const 1, ψ n)] := rfl

/-- **The buy-one trader is efficiently computable** whenever `ψ` is machine-nameable: the
single-trade certificate with the constant feature stream.
Source: FAF `EfficientlyComputable.ofSingleTradeBlocksBig` (`Framework/Machine/SpliceMachine.lean`); mandate § K3
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem buyOne_efficientlyComputable (ψ : ℕ → Sentence) (hψ : MachineSentenceCodes ψ) :
    EfficientlyComputable (buyOne ψ) :=
  EfficientlyComputable.ofSingleTradeBlocksBig (buyOne ψ) (fun _ => EF.const 1) ψ
    (MachineTokenStream.const _) (fun _ => trivial) hψ (fun _ => rfl)

/-- The buy-one trader's net worth: `∑_{i ≤ n} (payout_v (ψ i) − V i (ψ i))`.
Source: none: infrastructure (FAF `Trader.netWorth`, `Strategy.value`)
Kind: L
Fidelity: n/a -/
lemma buyOne_netWorth (ψ : ℕ → Sentence) (V : History) (v : PCWorld) (n : ℕ) :
    (buyOne ψ).netWorth V v n = ∑ i ∈ Finset.range (n + 1), (v.payout (ψ i) - V i (ψ i)) := by
  unfold Trader.netWorth
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Strategy.value, EF.denote_const]

/-- A finite set of sentences each in some stage lies in one stage.
Source: none: infrastructure (FAF `DeductiveProcess.mono_le`)
Kind: L
Fidelity: n/a -/
lemma exists_stage_of_finset (DP : DeductiveProcess) (ψ : ℕ → Sentence) (F : Finset ℕ)
    (h : ∀ j ∈ F, ∃ k, ψ j ∈ DP.D k) : ∃ K, ∀ j ∈ F, ψ j ∈ DP.D K := by
  induction F using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a F ha ih =>
      obtain ⟨K, hK⟩ := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
      obtain ⟨k, hk⟩ := h a (Finset.mem_insert_self a F)
      refine ⟨max K k, fun j hj => ?_⟩
      rcases Finset.mem_insert.1 hj with rfl | hj
      · exact DP.mono_le (le_max_right _ _) hk
      · exact DP.mono_le (le_max_left _ _) (hK j hj)

/-- **K3b — the buy-one trader exploits a cheap, infinitely-often-true family.** Over any
`Q`, `DP` with `hworld`, nonnegative prices, a family `ψ` whose partial price sums are bounded
by `C` (`hbdd`), a predicate `moved` holding on infinitely many days (`hmove`) on each of which
`ψ n` enters some stage of `DP` (`hdec`): `buyOne ψ` exploits `Q` relative to `DP`. Route:
`exploits_of_bddBelow_of_unbounded` — every plausible assessment is `≥ −C` (long positions),
and for every `B` the first `⌈B + C⌉₊ + 1` moved days have all entered by some stage `K`, so on
the day `max K (max F)` every consistent world pays them.
Source: [[bli-program]] §3.6(iii); desiderata I2; mandate § K3 (K3b); FAF
`exploits_of_bddBelow_of_unbounded` (`Properties/Support/Exploitation.lean:191`)
Kind: P
Fidelity: exact (`hmove` explicit — the mandate's honest form; `hbdd` generalizes `Summable ε`)
Hyps: (a) -/
theorem buyOne_exploits (Q : History) (DP : DeductiveProcess)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (ψ : ℕ → Sentence) (moved : ℕ → Prop)
    (hdec : ∀ n, moved n → ∃ k, ψ n ∈ DP.D k) (hmove : Set.Infinite {n | moved n})
    (C : ℝ) (hbdd : ∀ n, ∑ i ∈ Finset.range (n + 1), Q i (ψ i) ≤ C) :
    (buyOne ψ).Exploits Q DP := by
  refine exploits_of_bddBelow_of_unbounded _ _ _ C ?_ ?_
  · rintro x ⟨n, v, -, rfl⟩
    rw [buyOne_netWorth, Finset.sum_sub_distrib]
    have h1 : 0 ≤ ∑ i ∈ Finset.range (n + 1), v.payout (ψ i) :=
      Finset.sum_nonneg fun i _ => (payout_mem_Icc _ _).1
    linarith [hbdd n]
  · intro B
    obtain ⟨F, hFsub, hFcard⟩ := hmove.exists_subset_card_eq (⌈B + C⌉₊ + 1)
    obtain ⟨K, hK⟩ := exists_stage_of_finset DP ψ F fun j hj => hdec j (hFsub hj)
    set n := max K (F.sup id) with hn
    obtain ⟨v, hv⟩ := hworld n
    refine ⟨(buyOne ψ).netWorth Q v n, ⟨n, v, hv, rfl⟩, ?_⟩
    rw [buyOne_netWorth, Finset.sum_sub_distrib]
    have hpay : ∀ j ∈ F, v.payout (ψ j) = 1 := by
      intro j hj
      unfold PCWorld.payout
      rw [if_pos (hv _ (DP.mono_le (le_max_left _ _) (hK j hj)))]
    have hFsubrange : F ⊆ Finset.range (n + 1) := by
      intro j hj
      rw [Finset.mem_range]
      have : j ≤ F.sup id := Finset.le_sup (f := id) hj
      omega
    have h1 : ∑ j ∈ F, v.payout (ψ j) ≤ ∑ i ∈ Finset.range (n + 1), v.payout (ψ i) :=
      Finset.sum_le_sum_of_subset_of_nonneg hFsubrange fun i _ _ => (payout_mem_Icc _ _).1
    have h2 : ∑ j ∈ F, v.payout (ψ j) = (⌈B + C⌉₊ + 1 : ℕ) := by
      rw [Finset.sum_congr rfl hpay, Finset.sum_const, hFcard]; simp
    have h3 : (B + C) ≤ (⌈B + C⌉₊ : ℝ) := Nat.le_ceil _
    have h4 := hbdd n
    push_cast at h2
    linarith

/-- K3b with a summable price bound: `Q n (ψ n) ≤ ε n` and `Summable ε` give the bounded
partial sums `buyOne_exploits` needs (prices are nonnegative, so `ε` is).
Source: mandate § K3 (K3b: "`hprice : ∀ n, Q n (ψ n) ≤ ε n` with `Summable ε`")
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem buyOne_exploits_of_summable (Q : History) (DP : DeductiveProcess)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hQ : ∀ n φ, 0 ≤ Q n φ) (ψ : ℕ → Sentence) (moved : ℕ → Prop)
    (hdec : ∀ n, moved n → ∃ k, ψ n ∈ DP.D k) (hmove : Set.Infinite {n | moved n})
    (ε : ℕ → ℝ) (hprice : ∀ n, Q n (ψ n) ≤ ε n) (hε : Summable ε) :
    (buyOne ψ).Exploits Q DP := by
  refine buyOne_exploits Q DP hworld ψ moved hdec hmove (∑' n, ε n) fun n => ?_
  calc ∑ i ∈ Finset.range (n + 1), Q i (ψ i) ≤ ∑ i ∈ Finset.range (n + 1), ε i :=
        Finset.sum_le_sum fun i _ => hprice i
    _ ≤ ∑' n, ε n := hε.sum_le_tsum _ fun i _ => le_trans (hQ i (ψ i)) (hprice i)

/-- **No logical inductor is a cheap, infinitely-often-true family's base**: with
`[IsLogicalInductor Q DP]`, an e.c. `ψ` with bounded partial price sums and `hdec`/`hmove`
cannot exist.
Source: mandate § K3 (K3b); FAF `IsLogicalInductor.noExploit`
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem no_cheap_moving_family (Q : History) (DP : DeductiveProcess) [hLI : IsLogicalInductor Q DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (ψ : ℕ → Sentence) (hψ : MachineSentenceCodes ψ) (moved : ℕ → Prop)
    (hdec : ∀ n, moved n → ∃ k, ψ n ∈ DP.D k) (hmove : Set.Infinite {n | moved n})
    (C : ℝ) (hbdd : ∀ n, ∑ i ∈ Finset.range (n + 1), Q i (ψ i) ≤ C) : False :=
  hLI.noExploit (buyOne ψ) (buyOne_efficientlyComputable ψ hψ)
    (buyOne_exploits Q DP hworld ψ moved hdec hmove C hbdd)

/-! ## The conclusion of record -/

/-- **The day-`n` index of the degenerate table at `c`** (`0` if unlisted — never the case on
the index, by `Tabular.keys`).
Source: mandate § K3 (`todayIdx`)
Kind: D
Fidelity: exact -/
def todayIdx (deg : ℕ → ℕ) (n c : ℕ) : ℕ := (entryOf c (tableOfCode (deg n))).getD 0

/-- **The move sentence** of coordinate `χ n` on day `n`: "tomorrow's cell of `χ n` is not
today's", `∼ lit (n+1) (χ n) (todayIdx n (χ n))`.
Source: [[bli-program]] §3.6(iii); mandate § K3 (`ψ n`)
Kind: D
Fidelity: exact -/
def moveSentence (C : CellFamily DP) (deg : ℕ → ℕ) (χ : ℕ → ℕ) (n : ℕ) : Sentence :=
  ∼ C.cellLit (n + 1) (χ n) (todayIdx deg n (χ n))

/-- **K3 — no degenerate linked BLI over an inductor whose rounded prices move.** Over a
logical inductor `Q` for `DP` (with `hworld`), a `Tabular` system over `(C, index)` whose
degenerate table `deg n` is a candidate, and a coordinate family `χ` that is eventually pinned
with its move sentence eventually small (`hpin`), with the move-sentence family machine-nameable
(`hψ`), and moving infinitely often in the sense that the move sentence enters a stage
(`hmove`): no `P` satisfies `PCPσ ∧ E5σ ∧ E1x Q P ∧ Degenerate (stateOf C) S P deg`.
The inductor would price each move sentence at `0` from day `N` on (K3a), so the buy-one trader
on the move sentences would exploit it (K3b): partial price sums bounded by `N`.
**`hmove` is a hypothesis** (mandate § K3: the honest theorem; its instance is OPEN,
`leakQ_rounded_price_moves`), and so is `hψ` — see findings F-A3 on why the move-sentence family
is not obviously machine-nameable at B2 (`todayIdx` reads the market's price).
Source: [[bli-program]] §3.6(iii); desiderata I2; bli-paper-043; bli-soto-a-007; mandate § K3
Kind: C
Fidelity: weaker: `hmove` (entry of the move sentence into a stage, infinitely often) and `hψ` are hypotheses
Hyps: (a) K3a/K3b; `hmove`, `hψ`, `hpin` explicit -/
theorem no_degenerate_linked_bli (C : CellFamily DP) (index : ℕ → List ℕ) (S : StateSystem)
    (Q : History) [IsLogicalInductor Q DP] (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hT : Tabular C index S) (deg : ℕ → ℕ) (hdegmem : ∀ n, deg n ∈ S.states (n + 1))
    (χ : ℕ → ℕ)
    (hpin : ∃ N, ∀ n ≥ N, χ n ∈ pinned C index n ∧ moveSentence C deg χ n ∈ smallSet n)
    (hψ : MachineSentenceCodes (moveSentence C deg χ))
    (hmove : Set.Infinite {n | ∃ k, moveSentence C deg χ n ∈ DP.D k}) (P : History) :
    ¬ (PCPσ C (stateOf C) S P ∧ E5σ (stateOf C) S P ∧ E1x Q P ∧
      Degenerate (stateOf C) S P deg) := by
  rintro ⟨hcoh, hE5, hE1, hdeg⟩
  obtain ⟨N, hN⟩ := hpin
  have hzero : ∀ n ≥ N, Q n (moveSentence C deg χ n) = 0 := by
    intro n hn
    obtain ⟨hc, hsmall⟩ := hN n hn
    obtain ⟨r, hr, he⟩ := hT.keys (n + 1) (deg n) (hdegmem n) (χ n) (mem_pinned.1 hc).1
    have ht : todayIdx deg n (χ n) = r := by simp [todayIdx, he]
    unfold moveSentence
    rw [ht]
    exact degenerate_move_zero C index S Q P hT hcoh hE5 hE1 deg hdeg n (hdegmem n) hc hr he
      (by unfold moveSentence at hsmall; rwa [ht] at hsmall)
  refine no_cheap_moving_family Q DP hworld _ hψ (fun n => ∃ k, moveSentence C deg χ n ∈ DP.D k)
    (fun _ h => h) hmove N fun n => ?_
  calc ∑ i ∈ Finset.range (n + 1), Q i (moveSentence C deg χ i)
      ≤ ∑ i ∈ Finset.range (n + 1), (if i < N then (1 : ℝ) else 0) := by
        refine Finset.sum_le_sum fun i _ => ?_
        split_ifs with hi
        · exact (IsLogicalInductor.price_mem_Icc (P := Q) (DP := DP) i _).2
        · rw [hzero i (by omega)]
    _ ≤ N := by
        rw [Finset.sum_boole]
        have : ((Finset.range (n + 1)).filter (fun i => i < N)).card ≤ N := by
          calc ((Finset.range (n + 1)).filter (fun i => i < N)).card
              ≤ (Finset.range N).card := Finset.card_le_card (by
                intro i hi
                rw [Finset.mem_filter] at hi
                exact Finset.mem_range.2 hi.2)
            _ = N := Finset.card_range N
        exact_mod_cast this

/-- **Summability is not decorative** (desiderata I2, remark-level N−): if the family is priced
at `1` on every day, the buy-one trader's net worth in a world falsifying every `ψ i` is
`−(n+1)`, unbounded below — so no exploitation claim could go through `buyOne` without a
summable (or at least bounded) price sum.
Source: mandate § K3 (`degenerate_summable_needed`); desiderata I2
Kind: N-
Fidelity: n/a (a world-level computation, not an exploitation refutation)
Hyps: (a) -/
theorem degenerate_summable_needed (ψ : ℕ → Sentence) (Q : History) (hQ : ∀ n, Q n (ψ n) = 1)
    (v : PCWorld) (hv : ∀ n, ¬ v.Holds (ψ n)) (n : ℕ) :
    (buyOne ψ).netWorth Q v n = -((n : ℝ) + 1) := by
  rw [buyOne_netWorth]
  have : ∀ i ∈ Finset.range (n + 1), v.payout (ψ i) - Q i (ψ i) = -1 := by
    intro i _
    unfold PCWorld.payout
    rw [if_neg (hv i), hQ i]; ring
  rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range]
  simp

end Cleanroom.Bli.BliLinkage.AttemptA
