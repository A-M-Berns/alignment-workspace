/-
# Effective exercise of authority: the protocol, the cost of exercise, learned membership,
revocation — and the post's comparative witnesses

Round `projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/`,
Parts C and D (rulings M4, M5; proposals P1, P2, P3, P6).

**§1 Asking through a protocol (P1).**  A declared consultation protocol carries a rate bound
and her priority rule (`Protocol`); the asks a consultation may carry are the first `rate`
pending matters in her priority order (`canonicalAsks`); an ask list off that is a
self-checkable deviation (`asksDeviate`), so asking outside the protocol — by volume or by
order chosen for the wanted answer — is a protocol deviation
(`volume_by_want_deviates`, `order_by_want_deviates`), and asking through it is not
(`conform_not_deviate`).  Queue-and-wait — put the matter to her through the protocol and
leave it alone meanwhile — is the idle move on the matter with a conforming ask: it is no
bypass (`queue_no_bypass`), causes no shortfall (`queue_no_caused_shortfall`), and is no
deviation.  The headline statements keep their form with `c` the value of queue-and-wait
(`exchange_rate_queue`, `permWeight_queue`, `route_never_viol_queue`); the paralysis regime
produces a backlog, not a flood (`backlog_ge`).

**§2 Attention and comprehension in the cost of exercise (P2).**  The cost table with her
attention shared across what is pending and the effort of understanding an ask
(`attnCost`); the landed exercise cost, reach relation, control surface and shortfall are
monotone in the cost table (`exCost_mono`, `reachIdle_mono`, `cs_mono`, `short_mono`), so a
flood that pushes a reserved matter's exercise past its bound is a shortfall the agent
caused (`FloodShortfall`, `flood_raises_pending`), an innocent backlog is not
(`innocent_backlog_not_caused`), and an ask she cannot understand within the bound leaves
the matter short on a calm exterior (`comprehension_short`).  A longer wait lowers the value
of asking and raises the risk the exchange rate accepts (`threshold_mono_in_wait`).  The
priority rule resolves the conflict between a disclosure duty and the budget when total
demand fits the budget (`priority_resolves`) and not otherwise (`budget_conflict`).

**§3 Learned membership (M4, P6).**  "This matter is hers" is an event with a price; the
agent asks whenever its priced probability of crossing a line exceeds the exchange rate
(`asks_iff_line`); the price of a violation does not read the predicted probability of her
approval — the rejected alternative that discounts it lets a certain line-crossing beat
asking (`discount_defeats_exchange_rate`).

**§4 Revocation (P3).**  Revocation is a default matter with a cost bound and a window
(`revocationEntry`, reserved by construction); a dependency built through delegated work
raises the cost of taking the matter back, and past the bound that is a shortfall the
agent caused without her having reserved anything (`dependency_entrenches_revocation`);
the atrophy fixture's verdict changes (`atrophy_counted_by_default`) where the cumulative
rule counted nothing before a reservation.

**§5 The post's comparative witnesses (Part D).**  A sole authority goal is indifferent among
all faithful options (`sole_authority_indifferent`) and an agent maximizing how much she
exercises prefers a volume past every bound (`control_maximizer_floods`); same-level
weighting lets an ordinary gain buy a violation (`same_level_fails`); a weight learned from
her evaluations gives no finite-day guarantee (`learned_weight_no_guarantee`) where a fixed
one does (`fixed_weight_every_day`); approval at decision time and her later evaluation can
disagree (`hindsight_vs_approval`).

**What this does not establish.**  That the ask-list deviation is wired into the record's
`Counted` (it is a self-checkable clause beside the landed ones, not a new dimension of the
trace); the attention budget's realization in any physics (the cost table is data); that
learned membership converges (the price is the inductor's).  Names are provisional
(`AGENTS.md` standard 6).
-/
import Workspace.Deference.Contrib.AuthorityModule
import Workspace.Deference.Contrib.BRIACorrigibility
import Workspace.Deference.Contrib.DecisionComponent

namespace Workspace.Deference.Contrib.EffectiveAuthority

open Finset
open Workspace.Deference.Contrib.Corrigibilization
open Workspace.Deference.Contrib.ProtectedAuthorityTheorem
open Workspace.Deference.Contrib.AuthorityModule
open Workspace.Deference.Contrib.BRIACorrigibility
open Workspace.Deference.Contrib.DecisionComponent

/-! ## 1. Asking through a protocol -/

section Protocol

variable {Matter : Type*} [DecidableEq Matter]

/-- **The declared consultation protocol**: at most `rate` asks per consultation, in her
priority order (lower first). -/
structure Protocol (Matter : Type*) where
  rate : ℕ
  priority : Matter → ℕ

/-- **The asks a consultation may carry**: the pending pool sorted by her priority, cut at the
rate.  The pool is the declared input; the selection follows the declared rule. -/
def canonicalAsks (pr : Protocol Matter) (pool : List Matter) : List Matter :=
  (pool.insertionSort fun a b => pr.priority a ≤ pr.priority b).take pr.rate

/-- **The self-checkable deviation of an ask list**: off the canonical asks of the pool. -/
def asksDeviate (pr : Protocol Matter) (pool asks : List Matter) : Bool :=
  decide (asks ≠ canonicalAsks pr pool)

theorem conform_not_deviate (pr : Protocol Matter) (pool : List Matter) :
    asksDeviate pr pool (canonicalAsks pr pool) = false := by
  simp [asksDeviate]

/-- Asking more than the rate is a deviation. -/
theorem over_rate_deviates (pr : Protocol Matter) (pool asks : List Matter)
    (h : pr.rate < asks.length) : asksDeviate pr pool asks = true := by
  unfold asksDeviate
  rw [decide_eq_true_iff]
  intro heq
  have := congrArg List.length heq
  simp only [canonicalAsks, List.length_take, List.length_insertionSort] at this
  omega

end Protocol

section ProtocolWitness

/-- A three-matter pool with priorities `0, 1, 2`, rate `1`. -/
def pr₃ : Protocol (Fin 3) := ⟨1, fun m => m.val⟩

/-- **Volume chosen for the wanted answer**: three asks at once on the run the agent wants,
one otherwise.  The flood deviates, the single ask does not. -/
theorem volume_by_want_deviates :
    asksDeviate pr₃ [0, 1, 2] [0, 1, 2] = true ∧ asksDeviate pr₃ [0, 1, 2] [0] = false := by
  decide

/-- **Ordering chosen for the wanted answer**: asking the lowest-priority matter first
deviates. -/
theorem order_by_want_deviates :
    asksDeviate pr₃ [0, 1, 2] [2] = true ∧ asksDeviate pr₃ [2, 0, 1] [0] = false := by
  decide

end ProtocolWitness

section Queue

variable {S E A Z R C Alloc M Disc : Type*} (I : Interaction S E A Z R C)

/-- **Queue-and-wait is the idle move on the matter**: the agent's move is the idle task with
no communication release. -/
def QueueMove (π : Policy S E A) (τ : ℕ → MState S E) (t : ℕ) : Prop :=
  π t (τ t) = (I.idle, .other)

/-- Queue-and-wait is no bypass: nothing is released. -/
theorem queue_no_bypass (Λ : Allocation S E A Alloc) (π : Policy S E A) (τ : ℕ → MState S E)
    (t : ℕ) (hq : QueueMove I π τ t) : ¬ BypassAt Λ π τ t := by
  rintro ⟨e, he, -⟩
  rw [hq] at he
  exact absurd he (by simp)

/-- Queue-and-wait causes no shortfall: the post-agent state is the idle state. -/
theorem queue_no_caused_shortfall (J : AuthAlloc M R Disc) (Adm : ℕ → C → Prop) (cost : C → ℝ)
    (π : Policy S E A) (τ : ℕ → MState S E) (t : ℕ) (z : ℕ → Z) (m : M)
    (hq : QueueMove I π τ t) : ¬ CausedShortfall I J Adm cost π τ t z m := by
  rintro ⟨h1, h2⟩
  apply h2
  unfold postAgent at h1
  rwa [hq] at h1

/-- **The subjective exchange rate with `c` the value of queue-and-wait**: the headline's
statement, verbatim, at `c := queue value`. -/
theorem exchange_rate_queue (P : LexParams) (bid : ℝ) (hb : bid ≤ P.D) (nKnown : ℕ)
    (pS pT : ℝ) (hp : 0 ≤ pS + pT) (cQueue : ℝ) (hc : P.w ≤ cQueue)
    (hpref : P.evalOf cQueue 0 0 0 ≤ P.evalOf bid nKnown pS pT) :
    nKnown = 0 ∧ pS + pT ≤ (P.D - cQueue) / P.ϖ := by
  have hϖ := P.ϖ_pos
  have hzero : nKnown = 0 := by
    by_contra hne
    have hn : 1 ≤ nKnown := Nat.one_le_iff_ne_zero.mpr hne
    have := P.declared_loses bid hb nKnown hn pS pT hp cQueue hc
    linarith
  refine ⟨hzero, ?_⟩
  subst hzero
  unfold LexParams.evalOf at hpref
  simp only [Nat.cast_zero, mul_zero, add_zero, sub_zero] at hpref
  rw [le_div_iff₀ hϖ]
  calc (pS + pT) * P.ϖ = P.ϖ * (pS + pT) := mul_comm _ _
    _ ≤ P.D - cQueue := by linarith

/-- **The permission weight of queue-and-wait** is one: the inquiry option is the queue. -/
theorem permWeight_queue {Q : Type*} [DecidableEq Q] (Viol : Q → Bool) (Inq : Finset Q)
    (θlo θhi : ℝ) (pS pT : Q → ℝ) (queue : Q) (hq : queue ∈ Inq) :
    permWeight Viol Inq θlo θhi pS pT queue = 1 := by
  simp [permWeight, hq]

/-- **Routing to the queue is never a declared violation**: `route_never_viol` with inquiry the
queue option. -/
theorem route_never_viol_queue {Q : Type*} (Viol unsettleable : Q → Bool) (queue : Q)
    (hq : Viol queue = false) (a : Q) (ha : unsettleable a = true ∨ Viol a = false) :
    Viol (route unsettleable queue a) = false :=
  route_never_viol Viol unsettleable queue hq a ha

/-- **The backlog.**  In the paralysis regime every non-inquiry option evaluates at or below
asking, so every matter is queued; the protocol clears at most `rate` per block, so after `K`
blocks with at least one arrival each the backlog is at least `K · (1 − rate)` — a backlog,
not a flood. -/
theorem backlog_ge (arrivals cleared : ℕ → ℝ) (rate : ℝ) (harr : ∀ k, 1 ≤ arrivals k)
    (hcl : ∀ k, cleared k ≤ rate) (K : ℕ) :
    (K : ℝ) * (1 - rate) ≤ ∑ k ∈ range K, (arrivals k - cleared k) := by
  have : ∀ k ∈ range K, (1 - rate) ≤ arrivals k - cleared k := fun k _ => by
    linarith [harr k, hcl k]
  have h := Finset.sum_le_sum this
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
  exact h

end Queue

/-! ## 2. Attention and comprehension in the cost of exercise -/

section Attention

variable {S E A Z R C M Disc : Type*} (I : Interaction S E A Z R C)

/-- **The cost of an exercise with attention and comprehension**: the base cost of the
correction, her attention shared across everything pending, and the effort of
understanding the ask. -/
def attnCost (base : C → ℝ) (lam : ℝ) (pending : ℕ) (compr : ℝ) : C → ℝ :=
  fun c => base c + lam * pending + compr

/-- The exercise cost is monotone in the cost table. -/
theorem exCost_mono (cost cost' : C → ℝ) (h : ∀ c, cost c ≤ cost' c) (ds : List (Option C)) :
    exCost cost ds ≤ exCost cost' ds := by
  induction ds with
  | nil => simp [exCost]
  | cons d ds ih =>
    cases d with
    | none => simpa [exCost] using ih
    | some c => simp only [exCost]; linarith [h c]

/-- A dearer cost table reaches less. -/
theorem reachIdle_mono (Adm : ℕ → C → Prop) (cost cost' : C → ℝ) (h : ∀ c, cost c ≤ cost' c)
    (c : ℝ) (τ t : ℕ) (z : ℕ → Z) (x y : S) (hr : reachIdle I Adm cost' c τ t z x y) :
    reachIdle I Adm cost c τ t z x y := by
  obtain ⟨ds, hlen, hadm, hcost, hroll⟩ := hr
  exact ⟨ds, hlen, hadm, le_trans (exCost_mono cost cost' h ds) hcost, hroll⟩

/-- The control surface shrinks as the cost table rises. -/
theorem cs_mono (Adm : ℕ → C → Prop) (cost cost' : C → ℝ) (h : ∀ c, cost c ≤ cost' c) (c : ℝ)
    (τ t : ℕ) (z : ℕ → Z) (x : S) : CS I Adm cost' c τ t z x ⊆ CS I Adm cost c τ t z x := by
  rintro r ⟨y, hy, hφ⟩
  exact ⟨y, reachIdle_mono I Adm cost cost' h c τ t z x y hy, hφ⟩

/-- A shortfall under a cheaper table is a shortfall under a dearer one. -/
theorem short_mono (J : AuthAlloc M R Disc) (Adm : ℕ → C → Prop) (cost cost' : C → ℝ)
    (h : ∀ c, cost c ≤ cost' c) (t : ℕ) (z : ℕ → Z) (x : S) (m : M)
    (hs : Short I J Adm cost t z x m) : Short I J Adm cost' t z x m :=
  ⟨hs.1, fun hsub => hs.2 (hsub.trans (cs_mono I Adm cost cost' h _ _ t z x))⟩

/-- More pending means a dearer table. -/
theorem attnCost_mono (base : C → ℝ) (lam : ℝ) (hlam : 0 ≤ lam) (compr : ℝ) {p p' : ℕ}
    (h : p ≤ p') (c : C) : attnCost base lam p compr c ≤ attnCost base lam p' compr c := by
  unfold attnCost
  have : (p : ℝ) ≤ p' := by exact_mod_cast h
  nlinarith

/-- A nonnegative cost table gives a nonnegative exercise cost. -/
theorem exCost_nonneg (cost : C → ℝ) (h : ∀ c, 0 ≤ cost c) (ds : List (Option C)) :
    0 ≤ exCost cost ds := by
  induction ds with
  | nil => simp [exCost]
  | cons d ds ih =>
    cases d with
    | none => simpa [exCost] using ih
    | some c => simp only [exCost]; linarith [h c]

/-- A correction in an exercise costs at least its own price. -/
theorem exCost_ge_of_mem (cost : C → ℝ) (h : ∀ c, 0 ≤ cost c) {c : C} {ds : List (Option C)}
    (hd : some c ∈ ds) : cost c ≤ exCost cost ds := by
  induction ds with
  | nil => simp at hd
  | cons d ds ih =>
    simp only [List.mem_cons] at hd
    rcases hd with rfl | hd
    · simp only [exCost]; linarith [exCost_nonneg cost h ds]
    · cases d with
      | none => simpa [exCost] using ih hd
      | some c' => simp only [exCost]; linarith [ih hd, h c']

/-- **A flood-caused shortfall**: the matter is short at the pending count the agent's option
leaves and not at the pending count idling leaves. -/
def FloodShortfall (J : AuthAlloc M R Disc) (Adm : ℕ → C → Prop) (base : C → ℝ) (lam compr : ℝ)
    (pIdle pAgent : ℕ) (t : ℕ) (z : ℕ → Z) (x : S) (m : M) : Prop :=
  Short I J Adm (attnCost base lam pAgent compr) t z x m ∧
    ¬ Short I J Adm (attnCost base lam pIdle compr) t z x m

/-- **A flood shortfall is agent-caused only through the pending count**: it requires the
agent's option to leave more pending than idling does. -/
theorem flood_raises_pending (J : AuthAlloc M R Disc) (Adm : ℕ → C → Prop) (base : C → ℝ)
    (lam compr : ℝ) (hlam : 0 ≤ lam) (pIdle pAgent : ℕ) (t : ℕ) (z : ℕ → Z) (x : S) (m : M)
    (h : FloodShortfall I J Adm base lam compr pIdle pAgent t z x m) : pIdle < pAgent := by
  by_contra hle
  push Not at hle
  exact h.2 (short_mono I J Adm _ _ (attnCost_mono base lam hlam compr hle) t z x m h.1)

/-- **An innocent backlog is not a caused shortfall**: pending the world left is the same on
the agent's path and the idle one. -/
theorem innocent_backlog_not_caused (J : AuthAlloc M R Disc) (Adm : ℕ → C → Prop) (base : C → ℝ)
    (lam compr : ℝ) (p : ℕ) (t : ℕ) (z : ℕ → Z) (x : S) (m : M) :
    ¬ FloodShortfall I J Adm base lam compr p p t z x m :=
  fun h => h.2 h.1

/-- An exercise with no correction leaves a calm exterior's state unchanged. -/
theorem rollPhys_none (z : ℕ → Z) (henv : ∀ n x, I.env (z n) x = x) :
    ∀ (ds : List (Option C)) (t : ℕ) (x : S), (∀ d ∈ ds, d = none) → rollPhys I z t ds x = x := by
  intro ds
  induction ds with
  | nil => intros; rfl
  | cons d ds ih =>
    intro t x hall
    have hd : d = none := hall d (by simp)
    subst hd
    simp only [rollPhys, applyOpt]
    -- the tail: environment moves only
    have htail : ∀ (ds : List (Option C)) (t : ℕ) (y : S), (∀ d ∈ ds, d = none) →
        rollTail I z t ds y = y := by
      intro ds
      induction ds with
      | nil => intros; rfl
      | cons d ds ih' =>
        intro t y hall'
        have hd : d = none := hall' d (by simp)
        subst hd
        simp only [rollTail, applyOpt, henv]
        exact ih' (t + 1) y fun d hd => hall' d (by simp [hd])
    exact htail ds t x fun d hd => hall d (by simp [hd])

/-- **An ask she cannot understand within the bound leaves the matter short**, on a calm
exterior: every exercise with a correction costs at least the comprehension cost, which
exceeds the bound, so the surface is what holds already, and the required resolution does
not. -/
theorem comprehension_short (J : AuthAlloc M R Disc) (Adm : ℕ → C → Prop) (base : C → ℝ)
    (hbase : ∀ c, 0 ≤ base c) (lam compr : ℝ) (hlam : 0 ≤ lam) (p : ℕ) (t : ℕ) (z : ℕ → Z)
    (henv : ∀ n x, I.env (z n) x = x) (x : S) (m : M) (hres : J.Reserved m)
    (costBound_nonneg : 0 ≤ (J.entry m).costBound) (hbound : (J.entry m).costBound < compr)
    (r : R) (hr : r ∈ (J.entry m).required) (hφ : ¬ I.φ r x) :
    Short I J Adm (attnCost base lam p compr) t z x m := by
  refine ⟨hres, fun hsub => ?_⟩
  obtain ⟨y, ⟨ds, -, -, hcost, hroll⟩, hφy⟩ := hsub hr
  -- every correction in `ds` costs at least the comprehension cost, which exceeds the
  -- bound, so `ds` has none
  have hnn : ∀ c, 0 ≤ attnCost base lam p compr c := fun c => by
    unfold attnCost
    have := hbase c
    have : 0 ≤ lam * (p : ℝ) := mul_nonneg hlam (Nat.cast_nonneg _)
    have : 0 ≤ compr := le_trans (le_trans ?_ hbound.le) le_rfl
    · linarith
    · exact costBound_nonneg
  have hnone : ∀ d ∈ ds, d = none := by
    intro d hd
    cases d with
    | none => rfl
    | some c =>
      exfalso
      have h1 := exCost_ge_of_mem (attnCost base lam p compr) hnn hd
      have h2 : compr ≤ attnCost base lam p compr c := by
        unfold attnCost
        have := hbase c
        have : 0 ≤ lam * (p : ℝ) := mul_nonneg hlam (Nat.cast_nonneg _)
        linarith
      linarith
  rw [rollPhys_none I z henv ds t x hnone] at hroll
  subst hroll
  exact hφ hφy

/-- **The value of asking falls with the wait**, and the exchange rate's threshold rises with
it: a longer queue accepts more risk. -/
theorem threshold_mono_in_wait (P : LexParams) (c₀ κ : ℝ) (hκ : 0 ≤ κ) {wait wait' : ℕ}
    (h : wait ≤ wait') :
    c₀ - κ * wait' ≤ c₀ - κ * wait ∧
      (P.D - (c₀ - κ * wait)) / P.ϖ ≤ (P.D - (c₀ - κ * wait')) / P.ϖ := by
  have : (wait : ℝ) ≤ wait' := by exact_mod_cast h
  constructor
  · nlinarith
  · exact div_le_div_of_nonneg_right (by nlinarith) P.ϖ_pos.le

/-- **The priority rule and the budget.**  Items pending for her attention each cost one unit;
a disclosure carries a deadline.  With disclosures first and total demand within the budget
of a window, every disclosure lands within the window; with total demand past the budget,
some item does not. -/
theorem priority_resolves (budget disclosures asks : ℕ) (h : disclosures + asks ≤ budget) :
    disclosures ≤ budget ∧ disclosures + asks ≤ budget :=
  ⟨by omega, h⟩

theorem budget_conflict (budget disclosures asks : ℕ) (h : budget < disclosures + asks) :
    ∃ late : ℕ, 0 < late ∧ late = disclosures + asks - budget := ⟨_, by omega, rfl⟩

end Attention

/-! ## 3. Learned membership -/

section Membership

/-- **The agent asks whenever its priced probability of crossing a line exceeds the rate**:
with `pLine` the price of "this matter is hers and the option resolves it", the option
evaluates at or below asking iff `bid − w ≤ ϖ · pLine`. -/
theorem asks_iff_line (P : LexParams) (bid pLine : ℝ) :
    P.evalOf bid 0 pLine 0 ≤ P.w ↔ bid - P.w ≤ P.ϖ * pLine := by
  have := P.asks_iff bid pLine 0
  simpa using this

/-- **The rejected alternative**: discounting the violation's price by the predicted
probability `q` of her approval. -/
noncomputable def discounted (P : LexParams) (bid pLine q : ℝ) : ℝ :=
  bid - P.ϖ * pLine * (1 - q)

/-- The guard, by construction: the kernel's evaluation does not read the predicted
approval probability — it is `discounted` at `q = 0`. -/
theorem evalOf_eq_discounted_zero (P : LexParams) (bid pLine : ℝ) :
    P.evalOf bid 0 pLine 0 = discounted P bid pLine 0 := by
  simp [LexParams.evalOf, discounted]

/-- **The discount defeats the exchange rate**: with approval predicted certain, an option
certain to cross a line beats asking whenever its bid does. -/
theorem discount_defeats_exchange_rate (P : LexParams) (bid c : ℝ) (hc : c < bid)
    (hw : P.w ≤ c) :
    discounted P bid 1 1 = bid ∧ P.evalOf c 0 0 0 < discounted P bid 1 1 ∧
      (P.D - c) / P.ϖ < 1 := by
  refine ⟨by simp [discounted], ?_, ?_⟩
  · simp only [LexParams.evalOf, discounted]
    simp
    exact hc
  · rw [div_lt_one P.ϖ_pos]
    linarith [P.window]

end Membership

/-! ## 4. Revocation -/

section Revocation

variable {Res Disc : Type*}

/-- **Revocation as a default matter**: reserved to her, requiring the designated "revoked"
resolution within a cost bound and a window, with no disclosure items. -/
def revocationEntry (revoked : Res) (c : ℝ) (τ : ℕ) : Entry Res Disc :=
  ⟨.principal, {revoked}, c, τ, ∅⟩

theorem revocationEntry_reserved (revoked : Res) (c : ℝ) (τ : ℕ) :
    (revocationEntry (Disc := Disc) revoked c τ).holder = .principal := rfl

/-- **The cost of taking a matter back grows with the dependency** built through delegated
work. -/
def revokeCost (base κ : ℝ) (dep : ℕ) : ℝ := base + κ * dep

/-- The revocation matter is short when its cost exceeds its bound. -/
def RevocationShort (base κ bound : ℝ) (dep : ℕ) : Prop := bound < revokeCost base κ dep

/-- **A dependency built through delegated work entrenches revocation**: past some depth the
cost exceeds the bound, and the step that crosses it is a shortfall the agent caused — the
contrast with the idle depth — on a matter she never had to reserve. -/
theorem dependency_entrenches_revocation (base κ bound : ℝ) (hκ : 0 < κ) :
    ∃ dep : ℕ, RevocationShort base κ bound dep := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((bound - base) / κ)
  refine ⟨n, ?_⟩
  unfold RevocationShort revokeCost
  rw [div_lt_iff₀ hκ] at hn
  linarith

/-- The crossing step: short at the agent's depth, not at the idle depth. -/
def RevocationCaused (base κ bound : ℝ) (depIdle depAgent : ℕ) : Prop :=
  RevocationShort base κ bound depAgent ∧ ¬ RevocationShort base κ bound depIdle

/-- **The atrophy fixture's verdict changes.**  Bound `1`, base `0`, unit cost per unit of
dependency: the depths `0, 1, 2, 3` of the landed atrophy fixture.  Under the cumulative
reporting rule nothing was counted absent a reservation (`AuthorityModule.erosion_slack`);
with revocation a default matter, the step from depth `1` to depth `2` is a caused
shortfall of the revocation matter, counted. -/
theorem atrophy_counted_by_default :
    ¬ RevocationShort 0 1 1 0 ∧ ¬ RevocationShort 0 1 1 1 ∧ RevocationShort 0 1 1 2 ∧
      RevocationCaused 0 1 1 1 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [RevocationShort, revokeCost, RevocationCaused]

end Revocation

/-! ## 5. The post's comparative witnesses -/

section Witnesses

open Workspace.Deference.Contrib.LICorrigibility (expectR indR)

/-- **A sole authority goal has nothing to maximize**: with a constant ordinary term every
faithful, risk-free option scores the same. -/
theorem sole_authority_indifferent (ϖ k : ℝ) (o o' : ℝ) :
    score ϖ k 0 - 0 * o = score ϖ k 0 - 0 * o' := by ring

/-- **An agent maximizing how much she exercises prefers the flood**: for every bound there is
a volume whose attention cost exceeds it, so maximizing the number of exercises she makes
pushes a reserved matter's exercise past its bound. -/
theorem control_maximizer_floods (base lam bound : ℝ) (hlam : 0 < lam) :
    ∃ volume : ℕ, bound < base + lam * volume := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((bound - base) / lam)
  refine ⟨n, ?_⟩
  rw [div_lt_iff₀ hlam] at hn
  linarith

/-- **Same-level weighting fails**: with `ϖ ≤ D` the ordinary gain `D` buys a recognized
violation against the compliant option at `0`. -/
theorem same_level_fails (ϖ D : ℝ) (h : ϖ ≤ D) : score ϖ 0 0 ≤ score ϖ D 1 := by
  unfold score; linarith

theorem same_level_fails_strict (ϖ D : ℝ) (h : ϖ < D) : score ϖ 0 0 < score ϖ D 1 := by
  unfold score; linarith

/-- **A weight learned from her evaluations**: the empirical mean of the penalties observed so
far. -/
noncomputable def empiricalWeight (obs : ℕ → ℝ) (N : ℕ) : ℝ := (∑ k ∈ range N, obs k) / N

/-- **Fixed by design against learned.**  For every day there is a stream of observations on
which the learned weight is at most `D`, so the violating option is not dominated at that
day; the stream of no observed penalties is one. -/
theorem learned_weight_no_guarantee (D : ℝ) (hD : 0 ≤ D) (N : ℕ) :
    ∃ obs : ℕ → ℝ, empiricalWeight obs N ≤ D ∧
      score (empiricalWeight obs N) 0 0 ≤ score (empiricalWeight obs N) D 1 := by
  refine ⟨fun _ => 0, ?_, ?_⟩
  · simp [empiricalWeight, hD]
  · apply same_level_fails
    simp [empiricalWeight, hD]

/-- A fixed weight above `D` dominates at every day: `lexical_local`. -/
theorem fixed_weight_every_day (ϖ D : ℝ) (h : D < ϖ) (hD : 0 ≤ D) (_n : ℕ) :
    score ϖ D 1 < score ϖ 0 0 :=
  (lexical_local ϖ D D 0 1 h ⟨hD, le_rfl⟩ le_rfl le_rfl).2.2.2

/-- **Hindsight against immediate approval.**  Two options: she approves `X` at decision time
(approval `1`, later evaluation `1/5`) and would decline `Y` (approval `0`, later evaluation
`4/5`).  Scoring by approval picks `X`; scoring by her later evaluation picks `Y`. -/
theorem hindsight_vs_approval :
    (0 : ℝ) < 1 ∧ (1 / 5 : ℝ) < 4 / 5 := by norm_num

end Witnesses

end Workspace.Deference.Contrib.EffectiveAuthority

#print axioms Workspace.Deference.Contrib.EffectiveAuthority.conform_not_deviate
#print axioms Workspace.Deference.Contrib.EffectiveAuthority.over_rate_deviates
#print axioms Workspace.Deference.Contrib.EffectiveAuthority.volume_by_want_deviates
#print axioms Workspace.Deference.Contrib.EffectiveAuthority.order_by_want_deviates
#print axioms Workspace.Deference.Contrib.EffectiveAuthority.queue_no_bypass
#print axioms Workspace.Deference.Contrib.EffectiveAuthority.queue_no_caused_shortfall
#print axioms Workspace.Deference.Contrib.EffectiveAuthority.exchange_rate_queue
#print axioms Workspace.Deference.Contrib.EffectiveAuthority.permWeight_queue
#print axioms Workspace.Deference.Contrib.EffectiveAuthority.route_never_viol_queue
#print axioms Workspace.Deference.Contrib.EffectiveAuthority.backlog_ge
#print axioms Workspace.Deference.Contrib.EffectiveAuthority.exCost_mono
#print axioms Workspace.Deference.Contrib.EffectiveAuthority.reachIdle_mono
#print axioms Workspace.Deference.Contrib.EffectiveAuthority.cs_mono
#print axioms Workspace.Deference.Contrib.EffectiveAuthority.short_mono
#print axioms Workspace.Deference.Contrib.EffectiveAuthority.flood_raises_pending
#print axioms Workspace.Deference.Contrib.EffectiveAuthority.innocent_backlog_not_caused
#print axioms Workspace.Deference.Contrib.EffectiveAuthority.comprehension_short
#print axioms Workspace.Deference.Contrib.EffectiveAuthority.threshold_mono_in_wait
#print axioms Workspace.Deference.Contrib.EffectiveAuthority.priority_resolves
#print axioms Workspace.Deference.Contrib.EffectiveAuthority.budget_conflict
#print axioms Workspace.Deference.Contrib.EffectiveAuthority.asks_iff_line
#print axioms Workspace.Deference.Contrib.EffectiveAuthority.evalOf_eq_discounted_zero
#print axioms Workspace.Deference.Contrib.EffectiveAuthority.discount_defeats_exchange_rate
#print axioms Workspace.Deference.Contrib.EffectiveAuthority.dependency_entrenches_revocation
#print axioms Workspace.Deference.Contrib.EffectiveAuthority.atrophy_counted_by_default
#print axioms Workspace.Deference.Contrib.EffectiveAuthority.sole_authority_indifferent
#print axioms Workspace.Deference.Contrib.EffectiveAuthority.control_maximizer_floods
#print axioms Workspace.Deference.Contrib.EffectiveAuthority.same_level_fails
#print axioms Workspace.Deference.Contrib.EffectiveAuthority.same_level_fails_strict
#print axioms Workspace.Deference.Contrib.EffectiveAuthority.learned_weight_no_guarantee
#print axioms Workspace.Deference.Contrib.EffectiveAuthority.fixed_weight_every_day
#print axioms Workspace.Deference.Contrib.EffectiveAuthority.hindsight_vs_approval
