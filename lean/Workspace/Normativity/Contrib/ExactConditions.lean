/-
# Exact conditions on a price history: the dual-certified interface

Round `projects/normativity/rounds/2026-11-10-exact-conditions-capital/`.

A **condition** restricts which prices may be posted on each day: finitely many
**demanded bets** `g(x) = a·x + b` whose value at the posted prices must be nonnegative.
The force layer (`ProjectionForce`, `WarrantForce`) adds a penalty trader and obtains
conformance within a tolerance.  Here the prices satisfy the condition exactly, and what
the market absorbed to do so is one scalar **account**
`Q_N(W) = ∑_{n ≤ N} ∑_j μ_{n,j} g_{n,j}(W)`.

Everything is stated over an arbitrary price history carrying a dual certificate
(`DualCertifiedMarket`); no theorem in this file constructs one.  `ExactConditionsFloor`
does, for floor conditions.

* `DualCertifiedMarket` — the interface (A0).
* `account_le` — the account's ceiling `2 + ε` at every live world (A1).
* `no_efficient_trader_exploits`, `isLogicalInductor`, `account_unbounded_of_exploit`,
  `budgeted_netWorth_le` — an account bounded below preserves the criterion (A2).
* `account_nonneg_of_entailed`, `isLogicalInductor_of_entailed`, `deductive_exact` —
  conditions every live world satisfies are free (A3).
* `seller_netWorth_ge`, `seller_exploits`, `not_isLogicalInductor_of_seller` — a
  bounded-upside book against a compliant history (A5); no certificate is involved.
* `tighteningFloor_*`, `freshFloor_*` — two conditions no compliant history survives (A6).

Names are provisional (`AGENTS.md` standard 6).  Logical Induction's results are used as
the pinned dependency's theorems, not restated as axioms.
-/

import Workspace.Normativity.Contrib.AssessmentFirm
import Workspace.Normativity.Contrib.DeductiveRegion

namespace Workspace.Normativity.Contrib.ExactConditions

open LogicalInduction
open Workspace.Normativity.Contrib.AssessmentProcess
open Workspace.Normativity.Contrib.AssessmentFirm
open Workspace.Normativity.Contrib.DeductiveRegion

/-! ## Demanded bets -/

/-- A **demanded bet**: the affine function `g(x) = ∑ a·x(φ) + b` of a price vector,
carried as its trade list.  The condition it expresses is `0 ≤ g(prices)`. -/
structure Bet where
  /-- The `(coefficient, sentence)` terms. -/
  terms : List (ℚ × Sentence)
  /-- The constant. -/
  const : ℚ

namespace Bet

/-- The bet's value at a price or payout vector. -/
def eval (g : Bet) (x : Sentence → ℝ) : ℝ :=
  (g.terms.map fun t => (t.1 : ℝ) * x t.2).sum + (g.const : ℝ)

/-- The sentences the bet reads. -/
def support (g : Bet) : Finset Sentence := (g.terms.map Prod.snd).toFinset

lemma eval_congr (g : Bet) {x y : Sentence → ℝ} (h : ∀ φ ∈ g.support, x φ = y φ) :
    g.eval x = g.eval y := by
  unfold eval
  congr 2
  apply List.map_congr_left
  intro t ht
  rw [h t.2 (by
    simp only [support, List.mem_toFinset, List.mem_map]
    exact ⟨t, ht, rfl⟩)]

/-- Selling `c` units at prices `y`, settled at `x`, summed over the bet's terms. -/
lemma sum_terms_scaled (g : Bet) (c : ℝ) (x y : Sentence → ℝ) :
    (g.terms.map fun t => -c * (t.1 : ℝ) * (x t.2 - y t.2)).sum =
      c * g.eval y - c * g.eval x := by
  unfold eval
  induction g.terms with
  | nil => simp
  | cons t rest ih =>
      simp only [List.map_cons, List.sum_cons] at ih ⊢
      linarith

/-- The floor `c ≤ x(φ)` as a demanded bet. -/
def floor (φ : Sentence) (c : ℚ) : Bet := ⟨[(1, φ)], -c⟩

@[simp] lemma floor_eval (φ : Sentence) (c : ℚ) (x : Sentence → ℝ) :
    (floor φ c).eval x = x φ - (c : ℝ) := by
  simp [floor, eval, sub_eq_add_neg]

@[simp] lemma floor_support (φ : Sentence) (c : ℚ) : (floor φ c).support = {φ} := by
  simp [floor, support]

end Bet

/-! ## Conditions and their accounts -/

/-- A **condition**: for each day, finitely many demanded bets. -/
structure Condition where
  /-- The number of bets demanded on day `n`. -/
  count : ℕ → ℕ
  /-- The day-`n` bets; only indices below `count n` are read. -/
  bet : ℕ → ℕ → Bet

namespace Condition

variable (C : Condition)

/-- The day's rows hold at a price vector. -/
def Holds (n : ℕ) (x : Sentence → ℝ) : Prop := ∀ j, j < C.count n → 0 ≤ (C.bet n j).eval x

/-- The day's region `K_n`: cube points at which every row is nonnegative. -/
def Region (n : ℕ) (x : Sentence → ℝ) : Prop := (∀ φ, 0 ≤ x φ ∧ x φ ≤ 1) ∧ C.Holds n x

/-- The day's staked value `∑_j w_{n,j} g_{n,j}(x)`. -/
def stake (w : ℕ → ℕ → ℝ) (n : ℕ) (x : Sentence → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (C.count n), w n j * (C.bet n j).eval x

/-- **The account** `Q_N(x) = ∑_{n ≤ N} ∑_j w_{n,j} g_{n,j}(x)`. -/
def account (w : ℕ → ℕ → ℝ) (N : ℕ) (x : Sentence → ℝ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), C.stake w n x

/-- The sentences the day's rows read. -/
def daySupport (n : ℕ) : Finset Sentence :=
  (Finset.range (C.count n)).biUnion fun j => (C.bet n j).support

lemma holds_congr {n : ℕ} {x y : Sentence → ℝ} (h : ∀ φ ∈ C.daySupport n, x φ = y φ) :
    C.Holds n x ↔ C.Holds n y := by
  have key : ∀ j, j < C.count n → (C.bet n j).eval x = (C.bet n j).eval y := fun j hj =>
    Bet.eval_congr _ fun φ hφ =>
      h φ (Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hj, hφ⟩)
  constructor
  · intro hx j hj; rw [← key j hj]; exact hx j hj
  · intro hy j hj; rw [key j hj]; exact hy j hj

lemma stake_nonneg {w : ℕ → ℕ → ℝ} {n : ℕ} {x : Sentence → ℝ}
    (hw : ∀ j, j < C.count n → 0 ≤ w n j) (hx : C.Holds n x) : 0 ≤ C.stake w n x :=
  Finset.sum_nonneg fun j hj =>
    mul_nonneg (hw j (Finset.mem_range.mp hj)) (hx j (Finset.mem_range.mp hj))

/-- Every world live on a day satisfies that day's rows. -/
def Entailed (L : Assessment) : Prop := ∀ n v, L.Live n v → C.Holds n v.payout

/-- An entailed day's rows hold at every world live later: support-local nesting is
enough, because a day's rows read finitely many sentences. -/
lemma holds_of_live_later {L : Assessment} (hent : C.Entailed L) {n N : ℕ} (hnN : n ≤ N)
    {v : PCWorld} (hv : L.Live N v) : C.Holds n v.payout := by
  obtain ⟨v', hv', hagree⟩ := L.nested_le hnN (C.daySupport n) hv
  refine (C.holds_congr fun φ hφ => ?_).mp (hent n v' hv')
  rw [payout_eq_ratPayout, payout_eq_ratPayout, hagree φ hφ]

end Condition

lemma payout_cube (v : PCWorld) (φ : Sentence) : 0 ≤ v.payout φ ∧ v.payout φ ≤ 1 := by
  unfold PCWorld.payout
  split_ifs <;> constructor <;> norm_num

/-! ## A0 — the interface -/

/-- **A dual-certified market** (A0).  A rational price history `P` over an assessment
`L`, a condition `C` the prices satisfy exactly on every day, nonnegative multipliers
`mu`, and the **day inequality**: at every valuation `w` of the cube, the realized
trading firm's day value plus the day's multiplier-weighted bets is at most `eps n`.

The day inequality quantifies over cube valuations rather than worlds.  The pinned
market maker supports that form (`fixed_point_lemma_bounded` is stated over the cube, and
a strategy's value is affine in the valuation), and it is the form linear-programming
duality over `cube ∩ rows` produces.  The theorems of this file read it only at world
payouts. -/
structure DualCertifiedMarket where
  /-- The assessment the criterion is stated over. -/
  L : Assessment
  /-- The price history. -/
  P : History
  /-- Its exact rational quotes. -/
  quote : ℕ → Sentence → ℚ
  P_eq : ∀ day φ, P day φ = (quote day φ : ℝ)
  P_range : ∀ day φ, 0 ≤ P day φ ∧ P day φ ≤ 1
  /-- The condition. -/
  C : Condition
  /-- The multipliers. -/
  mu : ℕ → ℕ → ℝ
  mu_nonneg : ∀ n j, j < C.count n → 0 ≤ mu n j
  /-- Exact membership on every day. -/
  mem : ∀ n, C.Holds n (P n)
  /-- The day tolerances. -/
  eps : ℕ → ℝ
  eps_pos : ∀ n, 0 < eps n
  /-- A bound on the tolerances' partial sums. -/
  epsTotal : ℝ
  eps_sum_le : ∀ N, ∑ n ∈ Finset.range (N + 1), eps n ≤ epsTotal
  /-- The day inequality. -/
  day_le : ∀ n (w : Sentence → ℝ), (∀ φ, 0 ≤ w φ ∧ w φ ≤ 1) →
    ((tradingFirmTrader L quote).strat n).value P w + C.stake mu n w ≤ eps n

namespace DualCertifiedMarket

variable (M : DualCertifiedMarket)

/-- The realized trading firm. -/
noncomputable def firm : Trader := tradingFirmTrader M.L M.quote

/-- The account ceiling `U = 2 + ε`. -/
def U : ℝ := 2 + M.epsTotal

lemma epsTotal_pos : 0 < M.epsTotal := by
  have h := M.eps_sum_le 0
  rw [Finset.sum_range_one] at h
  exact lt_of_lt_of_le (M.eps_pos 0) h

lemma U_pos : 0 < M.U := by
  have := M.epsTotal_pos
  unfold U
  linarith

lemma region (n : ℕ) : M.C.Region n (M.P n) := ⟨M.P_range n, M.mem n⟩

/-- The summed day inequalities: firm value plus account, at any world. -/
theorem firm_add_account_le (N : ℕ) (v : PCWorld) :
    M.firm.netWorth M.P v N + M.C.account M.mu N v.payout ≤ M.epsTotal := by
  unfold Trader.netWorth Condition.account
  rw [← Finset.sum_add_distrib]
  exact (Finset.sum_le_sum fun n _ => M.day_le n v.payout (payout_cube v)).trans
    (M.eps_sum_le N)

/-! ## A1 — the account ceiling -/

/-- **Account ceiling** (A1).  At every world live at `N`, `Q_N ≤ 2 + ε`. -/
theorem account_le (N : ℕ) (v : PCWorld) (hv : M.L.Live N v) :
    M.C.account M.mu N v.payout ≤ M.U := by
  have h1 := M.firm_add_account_le N v
  have h2 := tradingFirmTrader_netWorth_floor M.L M.P M.P_range M.quote M.P_eq N v hv
  unfold U
  unfold firm at h1
  linarith

/-! ## A2 — preservation -/

/-- An account bounded below by `-B` on live prefixes. -/
def AccountBounded (B : ℝ) : Prop :=
  ∀ N v, M.L.Live N v → -B ≤ M.C.account M.mu N v.payout

/-- The realized firm's value is at most `ε + B`. -/
theorem firm_netWorth_le {B : ℝ} (hB : M.AccountBounded B) (N : ℕ) (v : PCWorld)
    (hv : M.L.Live N v) : M.firm.netWorth M.P v N ≤ M.epsTotal + B := by
  have h1 := M.firm_add_account_le N v
  have h2 := hB N v hv
  linarith

/-- **Preservation** (A2).  If the account is bounded below over live prefixes, no
efficiently computable trader exploits the history. -/
theorem no_efficient_trader_exploits {B : ℝ} (hB : M.AccountBounded B) (Tr : Trader)
    (hTr : EfficientlyComputable Tr) : ¬ M.L.Exploits Tr M.P := by
  intro hEx
  have hfirm := trading_firm_dominance M.L M.P M.P_range M.quote M.P_eq Tr hTr hEx
  apply hfirm.2
  refine ⟨M.epsTotal + B, ?_⟩
  rintro x ⟨n, v, hv, rfl⟩
  exact M.firm_netWorth_le hB n v hv

/-- **Preservation, criterion form** (A2).  A computable such history is a logical
inductor over the assessment. -/
theorem isLogicalInductor {B : ℝ} (hB : M.AccountBounded B)
    (hmarket : ComputableMarket M.P) : M.L.IsLogicalInductor M.P :=
  ⟨hmarket, fun Tr hTr => M.no_efficient_trader_exploits hB Tr hTr⟩

/-- **The one-way converse** (A2).  If an efficiently computable trader exploits the
history, the account is unbounded below over live prefixes. -/
theorem account_unbounded_of_exploit (Tr : Trader) (hTr : EfficientlyComputable Tr)
    (hEx : M.L.Exploits Tr M.P) (B : ℝ) :
    ∃ N v, M.L.Live N v ∧ M.C.account M.mu N v.payout < -B := by
  by_contra h
  exact M.no_efficient_trader_exploits (B := B)
    (fun N v hv => not_lt.mp fun hlt => h ⟨N, v, hv, hlt⟩) Tr hTr hEx

/-- **The quantitative form** (A2), for one budgeted component of the firm: its value,
scaled by its firm weight, is at most the ceiling minus the account.  No bound is claimed
for an unbudgeted trader. -/
theorem budgeted_netWorth_le (j r N : ℕ) (v : PCWorld) (hv : M.L.Live N v) :
    (tradingFirmWeight j (r + 1) : ℝ) *
        (AssessmentProcess.budgetedTrader M.L (firmRawTrader j) (r + 1) M.quote).netWorth
          M.P v N ≤ M.U - M.C.account M.mu N v.payout := by
  have h1 := M.firm_add_account_le N v
  have h2 := tradingFirmTrader_residual_floor M.L M.P M.P_range M.quote M.P_eq j r N v hv
  unfold U
  unfold firm at h1
  linarith

/-! ## A3 — entailed conditions are free -/

/-- **Entailed conditions cost nothing** (A3).  If every world live on a day satisfies
that day's rows, the account is nonnegative on live prefixes. -/
theorem account_nonneg_of_entailed (hent : M.C.Entailed M.L) (N : ℕ) (v : PCWorld)
    (hv : M.L.Live N v) : 0 ≤ M.C.account M.mu N v.payout :=
  Finset.sum_nonneg fun n hn =>
    M.C.stake_nonneg (M.mu_nonneg n)
      (M.C.holds_of_live_later hent (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)) hv)

theorem accountBounded_of_entailed (hent : M.C.Entailed M.L) : M.AccountBounded 0 :=
  fun N v hv => by simpa using M.account_nonneg_of_entailed hent N v hv

/-- **Entailed conditions preserve the criterion** (A3). -/
theorem isLogicalInductor_of_entailed (hent : M.C.Entailed M.L)
    (hmarket : ComputableMarket M.P) : M.L.IsLogicalInductor M.P :=
  M.isLogicalInductor (M.accountBounded_of_entailed hent) hmarket

/-- **The deductive instance** (A3).  A dual-certified market over a deductive process
whose day regions are the deductive regions of a scheduled fragment is unexploited, and
its prices on each scheduled fragment lie in the hull of the currently plausible truth
assignments — exactly, with no tolerance. -/
theorem deductive_exact (DP : DeductiveProcess)
    (hLive : ∀ n v, M.L.Live n v ↔ v.ConsistentWith (DP.D n))
    (coords : ℕ → List Sentence)
    (hreg : ∀ n (x : Sentence → ℝ), (∀ φ, 0 ≤ x φ ∧ x φ ≤ 1) →
      (M.C.Holds n x ↔ deductiveRegion (DP.D n) (coords n) x)) :
    (∀ Tr : Trader, EfficientlyComputable Tr → ¬ Tr.Exploits M.P DP) ∧
      ∀ n, deductiveRegion (DP.D n) (coords n) (M.P n) := by
  have hent : M.C.Entailed M.L := fun n v hv =>
    (hreg n v.payout (payout_cube v)).mpr
      (payout_mem_deductiveRegion (DP.D n) (coords n) v ((hLive n v).mp hv))
  refine ⟨fun Tr hTr hEx => ?_, fun n => (hreg n (M.P n) (M.P_range n)).mp (M.mem n)⟩
  apply M.no_efficient_trader_exploits (M.accountBounded_of_entailed hent) Tr hTr
  have hset : M.L.plausibleAssessments Tr M.P = Tr.plausibleAssessments M.P DP := by
    ext x
    constructor
    · rintro ⟨n, v, hv, rfl⟩; exact ⟨n, v, (hLive n v).mp hv, rfl⟩
    · rintro ⟨n, v, hv, rfl⟩; exact ⟨n, v, (hLive n v).mpr hv, rfl⟩
  unfold Assessment.Exploits
  rw [hset]
  exact hEx

/-- The deductive instance in the source's criterion. -/
theorem deductive_isLogicalInductor (DP : DeductiveProcess)
    (hLive : ∀ n v, M.L.Live n v ↔ v.ConsistentWith (DP.D n))
    (coords : ℕ → List Sentence)
    (hreg : ∀ n (x : Sentence → ℝ), (∀ φ, 0 ≤ x φ ∧ x φ ≤ 1) →
      (M.C.Holds n x ↔ deductiveRegion (DP.D n) (coords n) x))
    (hmarket : ComputableMarket M.P) (hprocess : ComputableDeductiveProcess DP) :
    IsLogicalInductor M.P DP :=
  ⟨hmarket, hprocess, (M.deductive_exact DP hLive coords hreg).1⟩

end DualCertifiedMarket

/-! ## A5 — obstruction

No certificate here: any history that satisfies the condition, any nonnegative staking. -/

lemma list_range_map_sum (f : ℕ → ℝ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ j ∈ Finset.range n, f j := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
      simp

lemma list_flatMap_map_sum {α β : Type*} (l : List α) (f : α → List β) (g : β → ℝ) :
    ((l.flatMap f).map g).sum = (l.map fun a => ((f a).map g).sum).sum := by
  induction l with
  | nil => simp
  | cons a rest ih =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
        List.sum_cons, ih]

namespace Condition

variable (C : Condition)

/-- The day-`n` strategy selling `w n j` units of each demanded bet.  Its coefficients are
rational constants, so it reads no price. -/
def sellStrategy (w : ℕ → ℕ → ℚ) (n : ℕ) : Strategy n where
  trades := (List.range (C.count n)).flatMap fun j =>
    (C.bet n j).terms.map fun t => (EF.const (-(w n j) * t.1), t.2)
  rank_le := by
    intro p hp
    simp only [List.mem_flatMap, List.mem_map] at hp
    obtain ⟨j, _, t, _, rfl⟩ := hp
    simp

/-- **The seller**: the trader that sells `w n j` units of each demanded bet. -/
def seller (w : ℕ → ℕ → ℚ) : Trader := ⟨C.sellStrategy w⟩

/-- The seller's day value: what the bets were worth at the posted prices, minus what
they are worth at the settling valuation. -/
theorem sellStrategy_value (w : ℕ → ℕ → ℚ) (n : ℕ) (P : History) (x : Sentence → ℝ) :
    (C.sellStrategy w n).value P x =
      C.stake (fun n j => (w n j : ℝ)) n (P n) - C.stake (fun n j => (w n j : ℝ)) n x := by
  unfold Strategy.value sellStrategy stake
  rw [list_flatMap_map_sum, list_range_map_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [List.map_map, ← Bet.sum_terms_scaled]
  congr 1
  apply List.map_congr_left
  intro t _
  simp only [Function.comp_apply, EF.denote, EF.denoteWith]
  push_cast
  ring

/-- **Obstruction, value form** (A5).  Against any history satisfying the condition, the
seller's cumulative value is at least minus the staked account, in every world. -/
theorem seller_netWorth_ge (w : ℕ → ℕ → ℚ) (hw : ∀ n j, 0 ≤ w n j) (P : History)
    (hmem : ∀ n, C.Holds n (P n)) (v : PCWorld) (N : ℕ) :
    -(C.account (fun n j => (w n j : ℝ)) N v.payout) ≤ (C.seller w).netWorth P v N := by
  unfold Trader.netWorth account
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun n _ => ?_
  change _ ≤ (C.sellStrategy w n).value P v.payout
  rw [sellStrategy_value]
  have h : 0 ≤ C.stake (fun n j => (w n j : ℝ)) n (P n) :=
    C.stake_nonneg (fun j _ => by exact_mod_cast hw n j) (hmem n)
  linarith

/-- **Obstruction** (A5).  If the staked account is bounded above over live prefixes and
unbounded below, the seller exploits every history satisfying the condition. -/
theorem seller_exploits (L : Assessment) (w : ℕ → ℕ → ℚ) (hw : ∀ n j, 0 ≤ w n j)
    (P : History) (hmem : ∀ n, C.Holds n (P n)) (Ub : ℝ)
    (hub : ∀ N v, L.Live N v → C.account (fun n j => (w n j : ℝ)) N v.payout ≤ Ub)
    (hunb : ∀ B : ℝ, ∃ N v, L.Live N v ∧
      C.account (fun n j => (w n j : ℝ)) N v.payout < -B) :
    L.Exploits (C.seller w) P := by
  refine ⟨⟨-Ub, ?_⟩, ?_⟩
  · rintro x ⟨N, v, hv, rfl⟩
    have h1 := C.seller_netWorth_ge w hw P hmem v N
    have h2 := hub N v hv
    linarith
  · rintro ⟨B, hB⟩
    obtain ⟨N, v, hv, hlt⟩ := hunb B
    have h1 := C.seller_netWorth_ge w hw P hmem v N
    have h2 := hB ⟨N, v, hv, rfl⟩
    linarith

/-- **Obstruction, criterion form** (A5).  If moreover the seller is efficiently
computable, no history satisfying the condition is a logical inductor over `L`. -/
theorem not_isLogicalInductor_of_seller (L : Assessment) (w : ℕ → ℕ → ℚ)
    (hw : ∀ n j, 0 ≤ w n j) (P : History) (hmem : ∀ n, C.Holds n (P n)) (Ub : ℝ)
    (hub : ∀ N v, L.Live N v → C.account (fun n j => (w n j : ℝ)) N v.payout ≤ Ub)
    (hunb : ∀ B : ℝ, ∃ N v, L.Live N v ∧
      C.account (fun n j => (w n j : ℝ)) N v.payout < -B)
    (heff : EfficientlyComputable (C.seller w)) : ¬ L.IsLogicalInductor P :=
  fun hLI => hLI.2 _ heff (C.seller_exploits L w hw P hmem Ub hub hunb)

end Condition

/-! ## One floor per day -/

/-- The condition demanding the single floor `c n ≤ price (φ n)` on day `n`. -/
def floors (φ : ℕ → Sentence) (c : ℕ → ℚ) : Condition where
  count _ := 1
  bet n _ := Bet.floor (φ n) (c n)

@[simp] lemma floors_holds (φ : ℕ → Sentence) (c : ℕ → ℚ) (n : ℕ) (x : Sentence → ℝ) :
    (floors φ c).Holds n x ↔ (c n : ℝ) ≤ x (φ n) := by
  unfold Condition.Holds floors
  constructor
  · intro h
    have := h 0 Nat.one_pos
    rw [Bet.floor_eval] at this
    linarith
  · intro h j _
    rw [Bet.floor_eval]
    linarith

@[simp] lemma floors_stake (φ : ℕ → Sentence) (c : ℕ → ℚ) (w : ℕ → ℕ → ℝ) (n : ℕ)
    (x : Sentence → ℝ) :
    (floors φ c).stake w n x = w n 0 * (x (φ n) - (c n : ℝ)) := by
  simp [Condition.stake, floors]

@[simp] lemma floors_daySupport (φ : ℕ → Sentence) (c : ℕ → ℚ) (n : ℕ) :
    (floors φ c).daySupport n = {φ n} := by
  simp [Condition.daySupport, floors]

lemma floors_account (φ : ℕ → Sentence) (c : ℕ → ℚ) (w : ℕ → ℕ → ℝ) (N : ℕ)
    (x : Sentence → ℝ) :
    (floors φ c).account w N x =
      ∑ n ∈ Finset.range (N + 1), w n 0 * (x (φ n) - (c n : ℝ)) := by
  simp [Condition.account]

/-- The constant-one history, which satisfies every floor at a level at most one. -/
def oneHistory : History := fun _ _ => 1

lemma oneHistory_holds (φ : ℕ → Sentence) (c : ℕ → ℚ) (hc : ∀ n, c n ≤ 1) (n : ℕ) :
    (floors φ c).Holds n (oneHistory n) := by
  rw [floors_holds]
  change ((c n : ℚ) : ℝ) ≤ 1
  exact_mod_cast hc n

lemma payout_of_holds {v : PCWorld} {φ : Sentence} (h : v.Holds φ) : v.payout φ = 1 := by
  simp [PCWorld.payout, h]

lemma payout_of_not_holds {v : PCWorld} {φ : Sentence} (h : ¬ v.Holds φ) :
    v.payout φ = 0 := by
  simp [PCWorld.payout, h]

/-! ## A6(a) — a floor tightening toward one on an undecided sentence -/

/-- The day-`n` level `1 - 2^-(n+1)`. -/
def tighteningLevel (n : ℕ) : ℚ := 1 - (1 / 2) ^ (n + 1)

lemma tighteningLevel_le_one (n : ℕ) : tighteningLevel n ≤ 1 := by
  unfold tighteningLevel
  have : (0 : ℚ) < (1 / 2) ^ (n + 1) := by positivity
  linarith

/-- The condition `1 - 2^-(n+1) ≤ price φ` on every day `n`. -/
def tighteningFloor (φ : Sentence) : Condition := floors (fun _ => φ) tighteningLevel

/-- One share a day. -/
def unitStake : ℕ → ℕ → ℚ := fun _ _ => 1

lemma sum_half_pow (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), (1 / 2 : ℝ) ^ (n + 1) = 1 - (1 / 2 : ℝ) ^ (N + 1) := by
  induction N with
  | zero => norm_num
  | succ N ih => rw [Finset.sum_range_succ, ih, pow_succ (1 / 2 : ℝ) (N + 1)]; ring

lemma tighteningFloor_account (φ : Sentence) (N : ℕ) (x : Sentence → ℝ) :
    (tighteningFloor φ).account (fun n j => (unitStake n j : ℝ)) N x =
      (N + 1 : ℝ) * (x φ - 1) + (1 - (1 / 2 : ℝ) ^ (N + 1)) := by
  unfold tighteningFloor
  rw [floors_account, ← sum_half_pow]
  have : ∀ n ∈ Finset.range (N + 1),
      ((unitStake n 0 : ℚ) : ℝ) * (x φ - ((tighteningLevel n : ℚ) : ℝ)) =
        (x φ - 1) + (1 / 2 : ℝ) ^ (n + 1) := by
    intro n _
    simp only [unitStake, tighteningLevel]
    push_cast
    ring
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range]
  simp

/-- Every demanded bet is nonnegative where `φ` is true. -/
theorem tighteningFloor_entailed_where_true (φ : Sentence) (v : PCWorld) (hv : v.Holds φ)
    (n : ℕ) : (tighteningFloor φ).Holds n v.payout := by
  unfold tighteningFloor
  rw [floors_holds, payout_of_holds hv]
  exact_mod_cast tighteningLevel_le_one n

/-- **A6(a), value form.**  Against every history satisfying the tightening floor, selling
one share a day is worth at least `-1` in every world and at least `N` after day `N` where
`φ` is false. -/
theorem tighteningFloor_seller_value (φ : Sentence) (P : History)
    (hmem : ∀ n, (tighteningFloor φ).Holds n (P n)) (v : PCWorld) (N : ℕ) :
    -1 ≤ ((tighteningFloor φ).seller unitStake).netWorth P v N ∧
      (¬ v.Holds φ → (N : ℝ) ≤ ((tighteningFloor φ).seller unitStake).netWorth P v N) := by
  have hge := (tighteningFloor φ).seller_netWorth_ge unitStake (fun _ _ => zero_le_one)
    P hmem v N
  rw [tighteningFloor_account] at hge
  have hpow : (0 : ℝ) < (1 / 2 : ℝ) ^ (N + 1) := by positivity
  have hN : (0 : ℝ) ≤ (N : ℝ) + 1 := by positivity
  constructor
  · have hle : ((N : ℝ) + 1) * (v.payout φ - 1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hN (by linarith [(payout_cube v φ).2])
    linarith
  · intro hφ
    rw [payout_of_not_holds hφ] at hge
    linarith

/-- **A6(a).**  If a world refuting `φ` is live on every day, selling one share a day
exploits every history satisfying the tightening floor. -/
theorem tighteningFloor_seller_exploits (φ : Sentence) (L : Assessment)
    (hopen : ∀ n, ∃ v, L.Live n v ∧ ¬ v.Holds φ) (P : History)
    (hmem : ∀ n, (tighteningFloor φ).Holds n (P n)) :
    L.Exploits ((tighteningFloor φ).seller unitStake) P := by
  refine ⟨⟨-1, ?_⟩, ?_⟩
  · rintro x ⟨N, v, _, rfl⟩
    exact (tighteningFloor_seller_value φ P hmem v N).1
  · rintro ⟨B, hB⟩
    obtain ⟨N, hN⟩ := exists_nat_gt B
    obtain ⟨v, hv, hφ⟩ := hopen N
    have h1 := (tighteningFloor_seller_value φ P hmem v N).2 hφ
    have h2 := hB ⟨N, v, hv, rfl⟩
    linarith

/-- **A6(a), criterion form.**  Efficiency of the seller is a hypothesis. -/
theorem tighteningFloor_not_isLogicalInductor (φ : Sentence) (L : Assessment)
    (hopen : ∀ n, ∃ v, L.Live n v ∧ ¬ v.Holds φ) (P : History)
    (hmem : ∀ n, (tighteningFloor φ).Holds n (P n))
    (heff : EfficientlyComputable ((tighteningFloor φ).seller unitStake)) :
    ¬ L.IsLogicalInductor P :=
  fun hLI => hLI.2 _ heff (tighteningFloor_seller_exploits φ L hopen P hmem)

/-! ## A6(b) — a fresh atom each day, settled the next -/

/-- The condition `1 - 2^-(n+1) ≤ price (atom n)` on day `n`. -/
def freshFloor : Condition := floors (fun n => .atom n) tighteningLevel

/-- `n` shares on day `n`. -/
def dayStake : ℕ → ℕ → ℚ := fun n _ => n

lemma sum_nat_mul_half_pow (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), (n : ℝ) * (1 / 2 : ℝ) ^ (n + 1) =
      1 - ((N : ℝ) + 2) * (1 / 2 : ℝ) ^ (N + 1) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, pow_succ (1 / 2 : ℝ) (N + 1)]
      push_cast
      ring

lemma freshFloor_account (N : ℕ) (x : Sentence → ℝ) :
    freshFloor.account (fun n j => (dayStake n j : ℝ)) N x =
      ∑ n ∈ Finset.range (N + 1),
        ((n : ℝ) * (1 / 2 : ℝ) ^ (n + 1) - (n : ℝ) * (1 - x (.atom n))) := by
  unfold freshFloor
  rw [floors_account]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [dayStake, tighteningLevel]
  push_cast
  ring

/-- The staked account of the fresh floors is at most `1` at every world, and at most
`1 - N` through day `N` where the day-`N` atom is false. -/
lemma freshFloor_account_le (v : PCWorld) (N : ℕ) :
    freshFloor.account (fun n j => (dayStake n j : ℝ)) N v.payout ≤ 1 ∧
      (¬ v.Holds (.atom N) →
        freshFloor.account (fun n j => (dayStake n j : ℝ)) N v.payout ≤ 1 - (N : ℝ)) := by
  rw [freshFloor_account, Finset.sum_sub_distrib, sum_nat_mul_half_pow]
  have hpow : (0 : ℝ) ≤ ((N : ℝ) + 2) * (1 / 2 : ℝ) ^ (N + 1) := by positivity
  have hterm : ∀ n ∈ Finset.range (N + 1),
      (0 : ℝ) ≤ (n : ℝ) * (1 - v.payout (.atom n)) := fun n _ =>
    mul_nonneg (Nat.cast_nonneg n) (by linarith [(payout_cube v (.atom n)).2])
  constructor
  · have := Finset.sum_nonneg hterm
    linarith
  · intro hφ
    have hlast : (N : ℝ) * (1 - v.payout (.atom N)) ≤
        ∑ n ∈ Finset.range (N + 1), (n : ℝ) * (1 - v.payout (.atom n)) :=
      Finset.single_le_sum hterm (Finset.self_mem_range_succ N)
    rw [payout_of_not_holds hφ] at hlast
    linarith

/-- **A6(b), value form.**  Against every history satisfying the fresh floors, selling `n`
shares of the day-`n` atom is worth at least `-1` in every world and at least `N - 1`
after day `N` where the day-`N` atom is false. -/
theorem freshFloor_seller_value (P : History) (hmem : ∀ n, freshFloor.Holds n (P n))
    (v : PCWorld) (N : ℕ) :
    -1 ≤ (freshFloor.seller dayStake).netWorth P v N ∧
      (¬ v.Holds (.atom N) → (N : ℝ) - 1 ≤ (freshFloor.seller dayStake).netWorth P v N) := by
  have hge := freshFloor.seller_netWorth_ge dayStake (fun n _ => Nat.cast_nonneg n)
    P hmem v N
  have hle := freshFloor_account_le v N
  constructor
  · linarith [hle.1]
  · intro hφ
    linarith [hle.2 hφ]

/-- **A6(b).**  If on every day a world refuting that day's atom is live, the seller
exploits every history satisfying the fresh floors. -/
theorem freshFloor_seller_exploits (L : Assessment)
    (hopen : ∀ n, ∃ v, L.Live n v ∧ ¬ v.Holds (.atom n)) (P : History)
    (hmem : ∀ n, freshFloor.Holds n (P n)) :
    L.Exploits (freshFloor.seller dayStake) P := by
  refine ⟨⟨-1, ?_⟩, ?_⟩
  · rintro x ⟨N, v, _, rfl⟩
    exact (freshFloor_seller_value P hmem v N).1
  · rintro ⟨B, hB⟩
    obtain ⟨N, hN⟩ := exists_nat_gt (B + 1)
    obtain ⟨v, hv, hφ⟩ := hopen N
    have h1 := (freshFloor_seller_value P hmem v N).2 hφ
    have h2 := hB ⟨N, v, hv, rfl⟩
    linarith

/-- **A6(b), criterion form.**  Efficiency of the seller is a hypothesis. -/
theorem freshFloor_not_isLogicalInductor (L : Assessment)
    (hopen : ∀ n, ∃ v, L.Live n v ∧ ¬ v.Holds (.atom n)) (P : History)
    (hmem : ∀ n, freshFloor.Holds n (P n))
    (heff : EfficientlyComputable (freshFloor.seller dayStake)) :
    ¬ L.IsLogicalInductor P :=
  fun hLI => hLI.2 _ heff (freshFloor_seller_exploits L hopen P hmem)

/-! ## Inhabitants for A5 and A6

The process revealing atom `k` on day `k + 1`: the worlds live at `N` are those affirming
atoms `0, …, N - 1`, so each day's atom is true in the limit and settled the next day. -/

/-- The deductive process revealing atoms `0, …, n - 1` by day `n`. -/
def revealProcess : DeductiveProcess where
  D n := (Finset.range n).image fun k => (.atom k : Sentence)
  mono n := Finset.image_subset_image (Finset.range_subset_range.mpr (Nat.le_succ n))

/-- The world affirming exactly the atoms below `N`. -/
def prefixWorld (N : ℕ) : PCWorld := boolPCWorld fun k => decide (k < N)

lemma prefixWorld_holds_atom (N k : ℕ) : (prefixWorld N).Holds (.atom k) ↔ k < N := by
  rw [PCWorld.holds_atom]
  simp [prefixWorld, boolPCWorld]

lemma prefixWorld_live (N : ℕ) : (ofDeductiveProcess revealProcess).Live N (prefixWorld N) := by
  intro φ hφ
  simp only [revealProcess, Finset.mem_image, Finset.mem_range] at hφ
  obtain ⟨k, hk, rfl⟩ := hφ
  exact (prefixWorld_holds_atom N k).mpr hk

lemma revealProcess_open (n : ℕ) :
    ∃ v, (ofDeductiveProcess revealProcess).Live n v ∧ ¬ v.Holds (.atom n) :=
  ⟨prefixWorld n, prefixWorld_live n, fun h => lt_irrefl n ((prefixWorld_holds_atom n n).mp h)⟩

/-- **A6(b) is inhabited**: a compliant history exists, every demand is settled true the
next day, and the seller exploits it. -/
theorem freshFloor_witness :
    (∀ n, freshFloor.Holds n (oneHistory n)) ∧
      (∀ n v, (ofDeductiveProcess revealProcess).Live (n + 1) v → v.Holds (.atom n)) ∧
      (ofDeductiveProcess revealProcess).Exploits (freshFloor.seller dayStake) oneHistory := by
  have hmem : ∀ n, freshFloor.Holds n (oneHistory n) :=
    oneHistory_holds _ _ tighteningLevel_le_one
  refine ⟨hmem, fun n v hv => ?_,
    freshFloor_seller_exploits _ revealProcess_open oneHistory hmem⟩
  exact hv _ (by
    simp only [revealProcess, Finset.mem_image, Finset.mem_range]
    exact ⟨n, Nat.lt_succ_self n, rfl⟩)

/-- **A5 is inhabited**: the hypothesis package of `Condition.seller_exploits` — an
assessment, a condition, a nonnegative staking, a history satisfying the condition, and a
staked account bounded above and unbounded below over live prefixes. -/
theorem seller_exploits_witness :
    (∀ n j, 0 ≤ dayStake n j) ∧ (∀ n, freshFloor.Holds n (oneHistory n)) ∧
      (∀ N v, (ofDeductiveProcess revealProcess).Live N v →
        freshFloor.account (fun n j => (dayStake n j : ℝ)) N v.payout ≤ 1) ∧
      ∀ B : ℝ, ∃ N v, (ofDeductiveProcess revealProcess).Live N v ∧
        freshFloor.account (fun n j => (dayStake n j : ℝ)) N v.payout < -B := by
  refine ⟨fun n _ => Nat.cast_nonneg n, oneHistory_holds _ _ tighteningLevel_le_one,
    fun N v _ => (freshFloor_account_le v N).1, fun B => ?_⟩
  obtain ⟨N, hN⟩ := exists_nat_gt (B + 1)
  refine ⟨N, prefixWorld N, prefixWorld_live N, ?_⟩
  have h := (freshFloor_account_le (prefixWorld N) N).2
    (fun h => lt_irrefl N ((prefixWorld_holds_atom N N).mp h))
  linarith

/-- The world refuting every atom. -/
def allFalse : PCWorld := boolPCWorld fun _ => false

lemma allFalse_not_holds_atom (k : ℕ) : ¬ allFalse.Holds (.atom k) := by
  rw [PCWorld.holds_atom]
  simp [allFalse, boolPCWorld]

/-- **A6(a) is inhabited**: over the process revealing nothing, both values of the atom
stay live, a compliant history exists, every demand is nonnegative where the atom is
true, and the seller exploits. -/
theorem tighteningFloor_witness :
    (∀ n, (tighteningFloor (.atom 0)).Holds n (oneHistory n)) ∧
      (∀ n, (ofDeductiveProcess emptyProcess).Live n allTrue ∧
        (ofDeductiveProcess emptyProcess).Live n allFalse) ∧
      (ofDeductiveProcess emptyProcess).Exploits
        ((tighteningFloor (.atom 0)).seller unitStake) oneHistory := by
  have hmem : ∀ n, (tighteningFloor (.atom 0)).Holds n (oneHistory n) :=
    oneHistory_holds _ _ tighteningLevel_le_one
  have hlive : ∀ n v, (ofDeductiveProcess emptyProcess).Live n v := fun n v φ hφ =>
    absurd hφ (by simp [emptyProcess])
  exact ⟨hmem, fun n => ⟨hlive n _, hlive n _⟩,
    tighteningFloor_seller_exploits _ _
      (fun n => ⟨allFalse, hlive n _, allFalse_not_holds_atom 0⟩) oneHistory hmem⟩

end Workspace.Normativity.Contrib.ExactConditions

#print axioms Workspace.Normativity.Contrib.ExactConditions.Bet.eval_congr
#print axioms Workspace.Normativity.Contrib.ExactConditions.Bet.sum_terms_scaled
#print axioms Workspace.Normativity.Contrib.ExactConditions.Condition.holds_of_live_later
#print axioms Workspace.Normativity.Contrib.ExactConditions.DualCertifiedMarket.firm_add_account_le
#print axioms Workspace.Normativity.Contrib.ExactConditions.DualCertifiedMarket.account_le
#print axioms Workspace.Normativity.Contrib.ExactConditions.DualCertifiedMarket.firm_netWorth_le
#print axioms Workspace.Normativity.Contrib.ExactConditions.DualCertifiedMarket.no_efficient_trader_exploits
#print axioms Workspace.Normativity.Contrib.ExactConditions.DualCertifiedMarket.isLogicalInductor
#print axioms Workspace.Normativity.Contrib.ExactConditions.DualCertifiedMarket.account_unbounded_of_exploit
#print axioms Workspace.Normativity.Contrib.ExactConditions.DualCertifiedMarket.budgeted_netWorth_le
#print axioms Workspace.Normativity.Contrib.ExactConditions.DualCertifiedMarket.account_nonneg_of_entailed
#print axioms Workspace.Normativity.Contrib.ExactConditions.DualCertifiedMarket.isLogicalInductor_of_entailed
#print axioms Workspace.Normativity.Contrib.ExactConditions.DualCertifiedMarket.deductive_exact
#print axioms Workspace.Normativity.Contrib.ExactConditions.DualCertifiedMarket.deductive_isLogicalInductor
#print axioms Workspace.Normativity.Contrib.ExactConditions.Condition.sellStrategy_value
#print axioms Workspace.Normativity.Contrib.ExactConditions.Condition.seller_netWorth_ge
#print axioms Workspace.Normativity.Contrib.ExactConditions.Condition.seller_exploits
#print axioms Workspace.Normativity.Contrib.ExactConditions.Condition.not_isLogicalInductor_of_seller
#print axioms Workspace.Normativity.Contrib.ExactConditions.tighteningFloor_entailed_where_true
#print axioms Workspace.Normativity.Contrib.ExactConditions.tighteningFloor_seller_value
#print axioms Workspace.Normativity.Contrib.ExactConditions.tighteningFloor_seller_exploits
#print axioms Workspace.Normativity.Contrib.ExactConditions.tighteningFloor_not_isLogicalInductor
#print axioms Workspace.Normativity.Contrib.ExactConditions.freshFloor_seller_value
#print axioms Workspace.Normativity.Contrib.ExactConditions.freshFloor_seller_exploits
#print axioms Workspace.Normativity.Contrib.ExactConditions.freshFloor_not_isLogicalInductor
#print axioms Workspace.Normativity.Contrib.ExactConditions.freshFloor_witness
#print axioms Workspace.Normativity.Contrib.ExactConditions.seller_exploits_witness
#print axioms Workspace.Normativity.Contrib.ExactConditions.tighteningFloor_witness
