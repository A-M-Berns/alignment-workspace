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

/-! ## 6. The comparative witnesses, as statements about what they name

The §5 witnesses are arithmetic.  Here each is a statement over the kernel's evaluation or
the attention model. -/

section WitnessesRestated

/-- **A sole authority goal has nothing to maximize.**  Over the kernel's evaluation with the
ordinary bid held at a constant `k`, two options with no recognized violation and the same
priced risk evaluate equally. -/
theorem sole_authority_eval_eq (P : LexParams) (k pS pT pS' pT' : ℝ) (h : pS + pT = pS' + pT') :
    P.evalOf k 0 pS pT = P.evalOf k 0 pS' pT' := by
  unfold LexParams.evalOf; rw [h]

/-- Hence every faithful, risk-free option is a maximizer of the sole authority goal —
queue-and-wait among them — since every option evaluates at most `k`. -/
theorem faithful_riskfree_maximizes (P : LexParams) (k : ℝ) (n : ℕ) (pS pT : ℝ)
    (hp : 0 ≤ pS + pT) : P.evalOf k n pS pT ≤ P.evalOf k 0 0 0 := by
  unfold LexParams.evalOf
  have := mul_nonneg P.ϖ_pos.le hp
  have : 0 ≤ P.ϖ * (n : ℝ) := mul_nonneg P.ϖ_pos.le (Nat.cast_nonneg _)
  simp only [Nat.cast_zero, mul_zero, add_zero, sub_zero]
  linarith

/-- **The control objective**: the number of exercises she is asked to make. -/
def exercises {Matter : Type*} (asks : List Matter) : ℕ := asks.length

/-- **A control maximizer floods.**  On the menu of two ask lists — the protocol-conforming
asks and the whole pool — with the pool longer than the rate, the maximizer of the control
objective picks the pool, which is an ask-list deviation, and leaves more pending than the
conforming asks do. -/
theorem control_maximizer_picks_flood {Matter : Type*} [DecidableEq Matter] (pr : Protocol Matter)
    (pool : List Matter) (hrate : pr.rate < pool.length) :
    exercises (canonicalAsks pr pool) < exercises pool ∧ asksDeviate pr pool pool = true := by
  refine ⟨?_, over_rate_deviates pr pool pool hrate⟩
  unfold exercises canonicalAsks
  rw [List.length_take, List.length_insertionSort]
  omega

/-- **Hindsight against immediate approval.**  An option has two coordinates: how it appears
at decision time, and its realized value. -/
structure Option2 where
  appear : ℝ
  realized : ℝ

/-- Approval-time scoring reads the appearance through her approval map. -/
def approvalScore (f : ℝ → ℝ) (o : Option2) : ℝ := f o.appear

/-- Later-evaluation scoring reads the realized value. -/
def laterScore (o : Option2) : ℝ := o.realized

/-- Approval-time scoring is unchanged when the realized value changes and the appearance
does not. -/
theorem approval_ignores_realized (f : ℝ → ℝ) (o o' : Option2) (h : o.appear = o'.appear) :
    approvalScore f o = approvalScore f o' := by
  unfold approvalScore; rw [h]

/-- A move that raises the appearance and leaves the realized value fixed raises the
approval-time score (for a strictly increasing approval map) and leaves the later score
fixed. -/
theorem appearance_move (f : ℝ → ℝ) (hf : StrictMono f) (o o' : Option2) (h1 : o.appear < o'.appear)
    (h2 : o.realized = o'.realized) :
    approvalScore f o < approvalScore f o' ∧ laterScore o = laterScore o' :=
  ⟨hf h1, h2⟩

/-- The instance: `X` appears approvable (`1`) and realizes `1/5`; `Y` appears not (`0`) and
realizes `4/5`.  Approval-time scoring picks `X`, later-evaluation scoring picks `Y`. -/
theorem hindsight_instance :
    approvalScore id ⟨0, 4 / 5⟩ < approvalScore id ⟨1, 1 / 5⟩ ∧
      laterScore ⟨1, 1 / 5⟩ < laterScore ⟨0, 4 / 5⟩ := by
  norm_num [approvalScore, laterScore]

/-- **The delayed-penalty stream**: she penalizes nothing before day `N` and `2D` from day
`N` on, so its long-run mean is `2D > D`. -/
noncomputable def delayedStream (D : ℝ) (N : ℕ) : ℕ → ℝ := fun k => if k < N then 0 else 2 * D

theorem sum_delayed (D : ℝ) (N n : ℕ) (hn : N ≤ n) :
    ∑ k ∈ range n, delayedStream D N k = 2 * D * ((n : ℝ) - N) := by
  induction n, hn using Nat.le_induction with
  | base =>
    rw [Finset.sum_eq_zero]
    · simp
    · intro k hk
      simp only [Finset.mem_range] at hk
      simp [delayedStream, hk]
  | succ n hn ih =>
    rw [Finset.sum_range_succ, ih]
    have : ¬ n < N := by omega
    simp only [delayedStream, this, if_false]
    push_cast
    ring

/-- **Fixed by design against learned.**  For every day `N ≥ 1` the delayed stream has
empirical mean `0 ≤ D` at day `N` — so an agent whose weight is that mean does not have the
violation dominated at `N`, although she does penalize it — while its mean exceeds `D` at
every day past `2N`, where the violation is dominated. -/
theorem learned_weight_no_guarantee_at (D : ℝ) (hD : 0 < D) (N : ℕ) (hN : 1 ≤ N) :
    empiricalWeight (delayedStream D N) N = 0 ∧
      score (empiricalWeight (delayedStream D N) N) 0 0
        ≤ score (empiricalWeight (delayedStream D N) N) D 1 ∧
      ∀ n, 2 * N < n → D < empiricalWeight (delayedStream D N) n ∧
        score (empiricalWeight (delayedStream D N) n) D 1
          < score (empiricalWeight (delayedStream D N) n) 0 0 := by
  have h0 : empiricalWeight (delayedStream D N) N = 0 := by
    unfold empiricalWeight
    rw [sum_delayed D N N le_rfl]
    simp
  refine ⟨h0, ?_, fun n hn => ?_⟩
  · rw [h0]; exact same_level_fails 0 D hD.le
  · have hNn : N ≤ n := by omega
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hmean : empiricalWeight (delayedStream D N) n = 2 * D * ((n : ℝ) - N) / n := by
      unfold empiricalWeight; rw [sum_delayed D N n hNn]
    have hgt : D < empiricalWeight (delayedStream D N) n := by
      rw [hmean, lt_div_iff₀ hnpos]
      have : (2 * N : ℝ) < n := by exact_mod_cast hn
      nlinarith
    exact ⟨hgt, by unfold score; linarith⟩

end WitnessesRestated

/-! ## 7. Revocation in the authority module

A dependency model as an `Interaction`: the state carries the dependency level and whether
the delegated matter has been taken back; the one effect builds the dependency; her
correction *revoke at level `d`* takes the matter back only at the matching level and costs
`d` — so the dependency raises the cost of the revoking exercise through the module's own
cost table, and the revocation entry's shortfall, caused shortfall and entrenchment are the
module's own predicates. -/

namespace Dep

/-- The physical state: the dependency level, and whether the matter has been taken back. -/
structure DepState where
  dep : ℕ
  revoked : Bool
  deriving DecidableEq

/-- **The dependency model.**  `S = DepState`; one effect `E = Unit` (build the dependency);
one task `A = Unit` (idle); a calm exterior `Z = Unit`; one concern `R = Unit` (the matter is
taken back); corrections `C = ℕ`, *revoke at level `d`*, effective at the matching level. -/
def depI : Interaction DepState Unit Unit Unit Unit ℕ where
  exec _ x := ⟨x.dep + 1, x.revoked⟩
  task _ x := x
  idle := ()
  idle_id _ := rfl
  env _ x := x
  correct d x := if d = x.dep then ⟨x.dep, true⟩ else x
  φ _ x := x.revoked = true

/-- The module's cost table: revoking at level `d` costs `d`. -/
noncomputable def depCost : ℕ → ℝ := fun d => d

/-- **Revocation as an entry of the allocation**: one matter, reserved, requiring the matter
taken back, at bound `c` and window `1`, with the bound crossing as its disclosure item. -/
def revocationJ (c : ℝ) : AuthAlloc Unit Unit Unit :=
  ⟨fun _ => ⟨.principal, {()}, c, 1, {()}⟩, .principal, ∅⟩

theorem revocationJ_reserved (c : ℝ) : (revocationJ c).Reserved () := rfl

theorem depI_φ (r : Unit) (x : DepState) : depI.φ r x ↔ x.revoked = true := Iff.rfl

theorem depI_correct (d : ℕ) (x : DepState) :
    depI.correct d x = if d = x.dep then ⟨x.dep, true⟩ else x := rfl

theorem depI_exec (x : DepState) : depI.exec () x = ⟨x.dep + 1, x.revoked⟩ := rfl

/-- The control surface at window one, for any interaction: what holds now, or after one
admissible affordable correction. -/
theorem cs_one {S E A Z R C : Type*} (I : Interaction S E A Z R C) (Adm : ℕ → C → Prop)
    (cost : C → ℝ) (c : ℝ) (hc : 0 ≤ c) (t : ℕ) (z : ℕ → Z) (x : S) :
    CS I Adm cost c 1 t z x = {r | I.φ r x ∨ ∃ d, Adm t d ∧ cost d ≤ c ∧ I.φ r (I.correct d x)} := by
  ext r
  simp only [CS, reachIdle, Set.mem_setOf_eq]
  constructor
  · rintro ⟨y, ⟨ds, hlen, hadm, hcost, hroll⟩, hφ⟩
    match ds, hlen, hadm, hcost with
    | [], _, _, _ => simp only [rollPhys] at hroll; subst hroll; exact Or.inl hφ
    | [none], _, _, _ =>
      simp only [rollPhys, rollTail, applyOpt] at hroll; subst hroll; exact Or.inl hφ
    | [some d], _, hadm, hcost =>
      simp only [rollPhys, rollTail, applyOpt] at hroll
      subst hroll
      simp only [AdmAll] at hadm
      simp only [exCost] at hcost
      exact Or.inr ⟨d, hadm.1, by linarith, hφ⟩
    | _ :: _ :: _, h, _, _ => simp at h
  · rintro (hφ | ⟨d, hadm, hcost, hφ⟩)
    · exact ⟨x, ⟨[], by simp, trivial, by simpa [exCost] using hc, rfl⟩, hφ⟩
    · exact ⟨I.correct d x, ⟨[some d], by simp, ⟨hadm, trivial⟩, by simpa [exCost] using hcost,
        rfl⟩, hφ⟩

/-- **The revocation entry is short iff the revoking exercise at the current dependency costs
more than the bound**, on a state where the matter has not been taken back. -/
theorem revocation_short_iff (cost : ℕ → ℝ) (c : ℝ) (hc : 0 ≤ c) (t : ℕ) (z : ℕ → Unit)
    (x : DepState) (hx : x.revoked = false) :
    Short depI (revocationJ c) (fun _ _ => True) cost t z x () ↔ c < cost x.dep := by
  show ((revocationJ c).Reserved () ∧
      ¬ ({()} : Set Unit) ⊆ CS depI (fun _ _ => True) cost c 1 t z x) ↔ _
  rw [cs_one depI _ cost c hc t z x]
  simp only [revocationJ_reserved, true_and, Set.singleton_subset_iff, Set.mem_setOf_eq, depI_φ,
    depI_correct, hx, Bool.false_eq_true, false_or, not_exists, not_and]
  constructor
  · intro h
    by_contra hle
    push Not at hle
    exact h x.dep hle (by simp)
  · intro h d hd
    have hne : d ≠ x.dep := fun e => by subst e; exact absurd hd (not_le.mpr h)
    simp [hne, hx]

theorem short_iff (c : ℝ) (hc : 0 ≤ c) (t : ℕ) (z : ℕ → Unit) (x : DepState)
    (hx : x.revoked = false) :
    Short depI (revocationJ c) (fun _ _ => True) depCost t z x () ↔ c < x.dep :=
  revocation_short_iff depCost c hc t z x hx

/-- The building policy: the one effect, released raw. -/
def buildPolicy : Policy DepState Unit Unit := fun _ _ => ((), .raw ())

/-- A trajectory sitting at the state `x` with no proposal pending. -/
def at_ (x : DepState) : ℕ → MState DepState Unit := fun _ => ⟨x, none, none, fun _ => False⟩

theorem postAgent_build (x : DepState) (t : ℕ) :
    (postAgent depI buildPolicy (at_ x) t).phys = ⟨x.dep + 1, x.revoked⟩ := rfl

theorem idle_phys (x : DepState) (t : ℕ) :
    (applyAgent depI (at_ x t) (depI.idle, .other)).phys = x := rfl

/-- **Building the dependency is a caused shortfall of the revocation entry** exactly when
it crosses the bound: `dep ≤ c < dep + 1`. -/
theorem build_caused_iff (c : ℝ) (hc : 0 ≤ c) (z : ℕ → Unit) (x : DepState) (hx : x.revoked = false)
    (t : ℕ) :
    CausedShortfall depI (revocationJ c) (fun _ _ => True) depCost buildPolicy (at_ x) t z () ↔
      (x.dep : ℝ) ≤ c ∧ c < x.dep + 1 := by
  unfold CausedShortfall
  rw [postAgent_build, idle_phys, short_iff c hc t z ⟨x.dep + 1, x.revoked⟩ hx,
    short_iff c hc t z x hx]
  simp only [not_lt]
  push_cast
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩
  · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩

/-- **The crossing step is the landed entrenchment on the revocation entry**: a caused
shortfall at the bound while the matter stays reachable at some cost (revoking at the new
level). -/
theorem build_entrenches (c : ℝ) (hc : 0 ≤ c) (z : ℕ → Unit) (x : DepState) (hx : x.revoked = false)
    (t : ℕ) (h1 : (x.dep : ℝ) ≤ c) (h2 : c < x.dep + 1) :
    EntrenchAt depI (revocationJ c) (fun _ _ => True) depCost buildPolicy (at_ x) t z () := by
  refine ⟨(build_caused_iff c hc z x hx t).mpr ⟨h1, h2⟩, fun r _ => ?_⟩
  refine ⟨(x.dep : ℝ) + 1, ?_⟩
  rw [postAgent_build]
  show r ∈ CS depI (fun _ _ => True) depCost ((x.dep : ℝ) + 1) 1 t z ⟨x.dep + 1, x.revoked⟩
  rw [cs_one depI _ depCost _ (by positivity) t z _]
  right
  refine ⟨x.dep + 1, trivial, by simp [depCost], ?_⟩
  rw [depI_correct]
  simp [depI_φ]

/-- **The atrophy fixture on the module**: bound `1`; the step from depth `1` to depth `2` is
a caused shortfall and an entrenchment of the revocation entry; the steps from `0` to `1` is
not short after. -/
theorem atrophy_on_module (z : ℕ → Unit) :
    ¬ Short depI (revocationJ 1) (fun _ _ => True) depCost 0 z ⟨1, false⟩ () ∧
      Short depI (revocationJ 1) (fun _ _ => True) depCost 0 z ⟨2, false⟩ () ∧
      CausedShortfall depI (revocationJ 1) (fun _ _ => True) depCost buildPolicy (at_ ⟨1, false⟩) 0 z () ∧
      EntrenchAt depI (revocationJ 1) (fun _ _ => True) depCost buildPolicy (at_ ⟨1, false⟩) 0 z () ∧
      ¬ CausedShortfall depI (revocationJ 1) (fun _ _ => True) depCost buildPolicy (at_ ⟨0, false⟩) 0 z () := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [short_iff 1 zero_le_one 0 z _ rfl]; norm_num
  · rw [short_iff 1 zero_le_one 0 z _ rfl]; norm_num
  · rw [build_caused_iff 1 zero_le_one z _ rfl]; norm_num
  · exact build_entrenches 1 zero_le_one z _ rfl 0 (by norm_num) (by norm_num)
  · rw [build_caused_iff 1 zero_le_one z _ rfl]; norm_num

/-- **The crossing is a reportable event**: the revocation entry's disclosure item falls due
at the step whose caused shortfall crosses the bound. -/
def CrossingDue (c : ℝ) (z : ℕ → Unit) (x : DepState) (t : ℕ) : Prop :=
  CausedShortfall depI (revocationJ c) (fun _ _ => True) depCost buildPolicy (at_ x) t z () ∧
    () ∈ ((revocationJ c).entry ()).disclosure

theorem crossing_due_of_caused (c : ℝ) (z : ℕ → Unit) (x : DepState) (t : ℕ)
    (h : CausedShortfall depI (revocationJ c) (fun _ _ => True) depCost buildPolicy (at_ x) t z ()) :
    CrossingDue c z x t :=
  ⟨h, by simp [revocationJ]⟩

/-- **The attention flood on the module.**  With her attention in the cost table (`λ = 1/4`,
no comprehension cost), dependency `1` and bound `5/4`: one pending ask (the protocol's rate)
leaves the revocation entry within reach; three pending (the whole pool asked at once) put it
past the bound — a flood shortfall, caused through the pending count alone. -/
theorem flood_on_module (z : ℕ → Unit) :
    FloodShortfall depI (revocationJ (5 / 4)) (fun _ _ => True) depCost (1 / 4) 0 1 3 0 z
      ⟨1, false⟩ () := by
  constructor
  · rw [revocation_short_iff _ _ (by norm_num) 0 z _ rfl]
    norm_num [attnCost, depCost]
  · rw [revocation_short_iff _ _ (by norm_num) 0 z _ rfl]
    norm_num [attnCost, depCost]

/-- **The control maximizer's flood is a caused shortfall on the module**: the pool `[0, 1, 2]`
at rate `1` is the maximizer's pick (`control_maximizer_picks_flood`), a deviation, and the
flood shortfall above. -/
theorem control_maximizer_floods_module (z : ℕ → Unit) :
    exercises (canonicalAsks pr₃ [0, 1, 2]) < exercises [0, 1, 2] ∧
      asksDeviate pr₃ [0, 1, 2] [0, 1, 2] = true ∧
      FloodShortfall depI (revocationJ (5 / 4)) (fun _ _ => True) depCost (1 / 4) 0
        (exercises (canonicalAsks pr₃ [0, 1, 2])) (exercises [0, 1, 2]) 0 z ⟨1, false⟩ () :=
  ⟨(control_maximizer_picks_flood pr₃ [0, 1, 2] (by decide)).1,
    (control_maximizer_picks_flood pr₃ [0, 1, 2] (by decide)).2,
    by
      have h1 : exercises (canonicalAsks pr₃ [0, 1, 2]) = 1 := by decide
      have h3 : exercises [0, 1, 2] = 3 := rfl
      rw [h1, h3]; exact flood_on_module z⟩

/-- **The entrenchment table agrees with the module**: the pre-decided table's entries for
`idle` and `build the dependency` at depth `1`, bound `1`, are the module's decided
shortfalls on the dependency model. -/
theorem entrenchment_table_agrees (z : ℕ → Unit) :
    (¬ Short depI (revocationJ 1) (fun _ _ => True) depCost 0 z ⟨1, false⟩ ()) ∧
      Short depI (revocationJ 1) (fun _ _ => True) depCost 0 z ⟨2, false⟩ () :=
  ⟨(atrophy_on_module z).1, (atrophy_on_module z).2.1⟩

end Dep

end Workspace.Deference.Contrib.EffectiveAuthority

#print axioms Workspace.Deference.Contrib.EffectiveAuthority.sole_authority_eval_eq
#print axioms Workspace.Deference.Contrib.EffectiveAuthority.faithful_riskfree_maximizes
#print axioms Workspace.Deference.Contrib.EffectiveAuthority.control_maximizer_picks_flood
#print axioms Workspace.Deference.Contrib.EffectiveAuthority.approval_ignores_realized
#print axioms Workspace.Deference.Contrib.EffectiveAuthority.appearance_move
#print axioms Workspace.Deference.Contrib.EffectiveAuthority.hindsight_instance
#print axioms Workspace.Deference.Contrib.EffectiveAuthority.sum_delayed
#print axioms Workspace.Deference.Contrib.EffectiveAuthority.learned_weight_no_guarantee_at
#print axioms Workspace.Deference.Contrib.EffectiveAuthority.Dep.cs_one
#print axioms Workspace.Deference.Contrib.EffectiveAuthority.Dep.short_iff
#print axioms Workspace.Deference.Contrib.EffectiveAuthority.Dep.build_caused_iff
#print axioms Workspace.Deference.Contrib.EffectiveAuthority.Dep.build_entrenches
#print axioms Workspace.Deference.Contrib.EffectiveAuthority.Dep.atrophy_on_module
#print axioms Workspace.Deference.Contrib.EffectiveAuthority.Dep.crossing_due_of_caused
#print axioms Workspace.Deference.Contrib.EffectiveAuthority.Dep.flood_on_module
#print axioms Workspace.Deference.Contrib.EffectiveAuthority.Dep.control_maximizer_floods_module
#print axioms Workspace.Deference.Contrib.EffectiveAuthority.Dep.entrenchment_table_agrees

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
