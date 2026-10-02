import Cleanroom.Bli.UdtBliTiling.SingleCoin

/-!
# `udt-bli-tiling` · Refreeze: the re-freezing dilemma on the sequential single-coin mugging
(T4(c)–(f), T8)

Over `SingleCoin.scPrior p` (one coin, `K` rounds, the utility summing every round):

* **The re-frozen policy** `refrozen t`: pay at `Ask_k` for `k < t`, and from round `t` on act by
  the two-step rule at `Σ = {coin}` — which is *proved* to be uniquely `refuse`
  (`refrozen_isTwoStepChoice`, from `SingleCoin.isTwoStepChoice_refuse`), and to be the one-step
  rule of the prior re-frozen on the coin-true class (`refrozen_isOneStepChoice_conditioned`,
  through `conditionOn_EU_eq_twoStepEU`). The definition is concrete; nothing about it is assumed.
* **Theorem B, two-sided** (`refreeze_dilemma`): for `t < K` and `gain = V(1−q) − cq > 0`,
  the frozen prior strictly prefers precommitting "pay at every round" to the re-frozen policy,
  by exactly `gain · ∑_{k ≥ t} γ_k` (`frozen_gap`), so `¬ NoStrictPrecommitAt (refrozen t) Ask_t`
  (`refreeze_not_noStrictPrecommitAt`); and the prior re-frozen on the coin strictly prefers the
  re-frozen policy to "pay at every round", by exactly `c · ∑_{k ≥ t} γ_k` (`refrozen_gap`). Both
  inequalities on one object, both gaps in closed form, both directions computed — the guard
  against "tiling defined so the un-refrozen agent trivially wins" (mandate T4 traps).
* **"Dynamic stability iff the prior never updates"** (T4(e)): over the class of policies that
  pay before `t` and are two-step at `Σ` from `t` on (`IsRefrozen Sig t`), no strict preference
  for precommitment holds iff the two-step decisions from `t` on agree with the one-step ones
  (= pay) (`stability_iff`); with `Σ = {coin}` that is `K ≤ t` — only the re-freeze that changes
  nothing tiles (`stability_coin_iff`); with `Σ = ∅` it always holds (`stability_empty`). The
  reading of "updates" as "the re-freeze changes a one-step decision at a positive-stake round"
  is the formalizer's, ATTRIBUTION-UNVETTED (findings).
* **Self-trust** (T8): `SelfTrustAgainst (scPrior p) coinClass payAll` holds (Kind `T`, from
  prior-optimality), and its content on the re-frozen one-step policy is the *same* gap as
  Theorem B's frozen side at `t = 0` (`selfTrust_is_refreeze_gap`).
* **Numerics**: the instance `(c, V) = (10, 100)`, `q = 1/2`, `K = 3`, `γ = 1`: `gain = 45`,
  threshold `10/11`; at `t = 1` the gaps are `90` (frozen) and `20` (re-frozen), at `t = 2` they
  are `45` and `10`. (The mandate's "`45` and `20`" pair does not occur at one `t`; findings.)

Sources: bli-soto-a-2-016 (Soto's conjecture — ATTRIBUTION-UNVETTED — and Abram's tiling aim),
bli-soto-a-2-017 (ii), bli-soto-a-084, bli-soto-b-038, bli-soto-b-034 D1; [[bli-program]] §3.9
U9(6); [[bli-program-construction]] X7; [[bli-program-desiderata]] I10 Theorem B (tiling half)
and U7; mandate T4(c)–(f), T8. The learning half of I10 is `udt-bli-learning`'s; nothing here
defines learning.
-/

namespace Cleanroom.Bli.UdtBliTiling

open Cleanroom.Bli.BliFinite Cleanroom.Bli.UdtBliCore Cleanroom.Bli.UdtBliSist Finset
open Cleanroom.Bli.UdtBliSist.Iter

namespace SingleCoin

variable {K : ℕ} (p : Params K)

/-! ## The re-frozen policy -/

/-- **The re-frozen policy from round `t` on**: pay at `Ask_k` for `k < t`, refuse at every other
table. The clause "refuse from `t` on" is what the two-step rule at `Σ = {coin}` prescribes
(`refrozen_isTwoStepChoice`), and what the prior re-frozen on the coin prescribes as its one-step
rule (`refrozen_isOneStepChoice_conditioned`): the definition is concrete, the identification is
a theorem. At `Rec_k` and `Other` nothing is at stake; the policy says `refuse` there.
Source: bli-soto-a-2-016 (`P_σ`, `σ = {coin}`), bli-soto-a-2-017 (ii) ("`P^(k)` refuses from
`t_k` on while `P^(0)` pays forever"); mandate §3.4, T4(c)
Kind: D
Fidelity: exact (one re-freeze day `t`; a schedule is the composition of such) -/
def refrozen (t : ℕ) : Policy (iterTables K) Bool :=
  fun T => decide (T.1 (coin1 K) = 1 ∧ ∃ k : Fin K, k.val < t ∧ T.1 (node1 K k) = 1)

/-- The re-frozen policy at `Ask_k`: pay iff `k < t`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma refrozen_askT (t : ℕ) (k : Fin K) : refrozen t (askT K k) = decide (k.val < t) := by
  unfold refrozen
  have hn : ∀ k' : Fin K, (askT K k).1 (node1 K k') = if k' = k then 1 else 0 :=
    fun k' => iterTable_some_node K true k k'
  simp only [askT_coin, hn, true_and]
  apply decide_eq_decide.mpr
  constructor
  · rintro ⟨k', hk', h⟩
    by_cases e : k' = k
    · subst e; exact hk'
    · rw [if_neg e] at h; norm_num at h
  · intro h; exact ⟨k, h, by simp⟩

/-- The re-frozen policy pays at `Ask_k` for `k < t`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma refrozen_askT_of_lt (t : ℕ) (k : Fin K) (hk : k.val < t) : refrozen t (askT K k) = true := by
  rw [refrozen_askT]; exact decide_eq_true hk

/-- The re-frozen policy refuses at `Ask_k` for `t ≤ k`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma refrozen_askT_of_le (t : ℕ) (k : Fin K) (hk : t ≤ k.val) : refrozen t (askT K k) = false := by
  rw [refrozen_askT]; exact decide_eq_false (not_lt.mpr hk)

/-- **The weight of the rounds from `t` on**: `∑_{k ≥ t} γ_k`.
Source: mandate T4(d) (the gap's closed form)
Kind: D
Fidelity: exact -/
def tailSum (γ : Fin K → ℚ) (t : ℕ) : ℚ := ∑ k, if t ≤ k.val then γ k else 0

/-- `roundSum (refrozen t) = ∑_{k < t} γ_k`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma roundSum_refrozen (t : ℕ) :
    roundSum p.γ (refrozen t) = ∑ k, if k.val < t then p.γ k else 0 := by
  unfold roundSum
  apply Finset.sum_congr rfl
  intro k _
  rw [refrozen_askT]
  by_cases h : k.val < t <;> simp [h, ind]

/-- `roundSum payAll − roundSum (refrozen t) = tailSum γ t`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma roundSum_payAll_sub_refrozen (t : ℕ) :
    roundSum p.γ payAll - roundSum p.γ (refrozen t) = tailSum p.γ t := by
  rw [roundSum_payAll, roundSum_refrozen]
  unfold tailSum
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  by_cases h : k.val < t
  · rw [if_pos h, if_neg (not_le.mpr h)]; ring
  · rw [if_neg h, if_pos (not_lt.mp h)]; ring

/-- The tail weight is positive when some round `k ≥ t` exists and the weights are positive.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tailSum_pos (hγ : ∀ k, 0 < p.γ k) (t : ℕ) (ht : t < K) : 0 < tailSum p.γ t := by
  unfold tailSum
  have hle : (if t ≤ (⟨t, ht⟩ : Fin K).val then p.γ ⟨t, ht⟩ else 0) ≤
      ∑ k, if t ≤ k.val then p.γ k else 0 := by
    apply Finset.single_le_sum (f := fun k : Fin K => if t ≤ k.val then p.γ k else 0)
    · intro k _; split_ifs
      · exact (hγ k).le
      · exact le_rfl
    · exact Finset.mem_univ _
  simp only [le_refl, if_true] at hle
  exact lt_of_lt_of_le (hγ _) hle

/-! ## Theorem B, the frozen side -/

/-- **The frozen prior's gap**: `𝔼[U | pp = payAll] − 𝔼[U | pp = refrozen t] = gain · ∑_{k ≥ t} γ_k`
(exact, `K` symbolic).
Source: bli-soto-a-2-017 (ii); [[bli-program-desiderata]] I10 Theorem B; mandate T4(d)
Kind: C (`exAnteValue_eq`)
Fidelity: exact
Hyps: (a) none; does not use faith -/
theorem frozen_gap (t : ℕ) :
    (scPrior p).exAnteValue payAll - (scPrior p).exAnteValue (refrozen t) =
      gain p * tailSum p.γ t := by
  rw [exAnteValue_eq, exAnteValue_eq, ← roundSum_payAll_sub_refrozen]
  ring

/-- **The frozen prior strictly prefers precommitting "pay at every round" to the re-frozen
policy** whenever a round `t < K` is re-frozen and `gain > 0`.
Source: bli-soto-a-2-017 (ii) ("`P^(0)` strictly prefers the un-refrozen policy"); bli-soto-b-038;
mandate T4(d)
Kind: C
Fidelity: exact
Hyps: (a) `0 < gain`, `0 < γ_k`, `t < K`; does not use faith -/
theorem frozen_prefers_payAll (t : ℕ) (ht : t < K) (hg : 0 < gain p) (hγ : ∀ k, 0 < p.γ k) :
    (scPrior p).exAnteValue (refrozen t) < (scPrior p).exAnteValue payAll := by
  have := frozen_gap p t
  have := tailSum_pos p hγ t ht
  nlinarith

/-- **Tiling fails at the first changed round**: `¬ NoStrictPrecommitAt (refrozen t) Ask_t` for
`t < K`, `gain > 0` — the one-point precommitment "pay at `Ask_t`" is strictly better, by
`gain · γ_t`.
Source: bli-soto-a-2-016 ("`P` strictly prefers precommitting against `σ` at the first node where
the coin is known"); [[bli-program]] §3.9 U9(6); mandate T4(d)
Kind: C (`roundSum_update`, `exAnteValue_eq`)
Fidelity: exact
Hyps: (a) `0 < gain`, `0 < γ_t`, `t < K`; does not use faith -/
theorem refreeze_not_noStrictPrecommitAt (t : ℕ) (ht : t < K) (hg : 0 < gain p)
    (hγ : ∀ k, 0 < p.γ k) :
    ¬ NoStrictPrecommitAt (scPrior p) (refrozen t) (askT K ⟨t, ht⟩) := by
  apply not_noStrictPrecommitAt_of_lt (b := true) ((structure_facts p).1 _)
  rw [exAnteValue_eq, exAnteValue_eq, roundSum_update, refrozen_askT_of_le t ⟨t, ht⟩ (le_refl _)]
  simp only [ind_true, ind_false, sub_zero, mul_one]
  nlinarith [hγ ⟨t, ht⟩]

/-! ## Theorem B, the re-frozen side -/

/-- **The re-frozen prior's gap**: under `conditionOn coinClass`,
`𝔼'[U | pp = refrozen t] − 𝔼'[U | pp = payAll] = c · ∑_{k ≥ t} γ_k`.
Source: bli-soto-a-2-017 (ii); mandate T4(d) ("the re-frozen prior strictly prefers its own
policy")
Kind: C (`conditionOn_exAnteValue_eq`)
Fidelity: exact
Hyps: (a) `0 < q`; does not use faith -/
theorem refrozen_gap (hq : 0 < p.q) (t : ℕ) :
    (conditionOn (scPrior p) (coinClass K) (coinClass_pos p hq)).exAnteValue (refrozen t) -
      (conditionOn (scPrior p) (coinClass K) (coinClass_pos p hq)).exAnteValue payAll =
      p.c * tailSum p.γ t := by
  rw [conditionOn_exAnteValue_eq p _ hq, conditionOn_exAnteValue_eq p _ hq,
    ← roundSum_payAll_sub_refrozen]
  ring

/-- **The re-frozen prior strictly prefers the re-frozen policy** to "pay at every round", for
`t < K`, `c > 0`.
Source: bli-soto-a-2-017 (ii); mandate T4(d)
Kind: C
Fidelity: exact
Hyps: (a) `0 < q`, `0 < c`, `0 < γ_k`, `t < K`; does not use faith -/
theorem refrozen_prefers_refrozen (hq : 0 < p.q) (hc : 0 < p.c) (hγ : ∀ k, 0 < p.γ k) (t : ℕ)
    (ht : t < K) :
    (conditionOn (scPrior p) (coinClass K) (coinClass_pos p hq)).exAnteValue payAll <
      (conditionOn (scPrior p) (coinClass K) (coinClass_pos p hq)).exAnteValue (refrozen t) := by
  have := refrozen_gap p hq t
  have := tailSum_pos p hγ t ht
  nlinarith

/-- **From round `t` on, the re-frozen policy is the two-step rule at `Σ = {coin}`**, uniquely.
Source: mandate T4(c) ("prove the two-step choice is unique and equals `refuse`")
Kind: C (`isTwoStepChoice_refuse`)
Fidelity: exact
Hyps: (a) `0 < q`, `0 < c`, `0 < γ_k`; does not use faith -/
theorem refrozen_isTwoStepChoice (hq : 0 < p.q) (hc : 0 < p.c) (hγ : ∀ k, 0 < p.γ k) (t : ℕ)
    (k : Fin K) (hk : t ≤ k.val) :
    IsTwoStepChoice (scPrior p) {coin1 K} (askT K k) (refrozen t (askT K k)) ∧
      ∀ b, IsTwoStepChoice (scPrior p) {coin1 K} (askT K k) b → b = refrozen t (askT K k) := by
  rw [refrozen_askT_of_le t k hk]
  obtain ⟨h1, h2⟩ := isTwoStepChoice_refuse p k hq hc (hγ k)
  refine ⟨h1, fun b hb => ?_⟩
  cases b
  · rfl
  · exact absurd hb h2

/-- **From round `t` on, the re-frozen policy is one-step UDT over the prior re-frozen on the
coin**; before `t` it is one-step UDT over the frozen prior (when `gain > 0`).
Source: bli-soto-a-2-016 (`P_σ` as a prior); mandate §3.4, T4(c)
Kind: C (`conditionOn_EU_eq_twoStepEU`, `isTwoStepChoice_refuse`, `isOneStepChoice_pay`)
Fidelity: exact
Hyps: (a) `0 < q`, `0 < c`, `0 < γ_k`, `0 < gain`; does not use faith -/
theorem refrozen_isOneStepChoice_conditioned (hq : 0 < p.q) (hc : 0 < p.c) (hg : 0 < gain p)
    (hγ : ∀ k, 0 < p.γ k) (t : ℕ) (k : Fin K) :
    (t ≤ k.val → (conditionOn (scPrior p) (coinClass K) (coinClass_pos p hq)).IsOneStepChoice
        (askT K k) (refrozen t (askT K k))) ∧
      (k.val < t → (scPrior p).IsOneStepChoice (askT K k) (refrozen t (askT K k))) := by
  constructor
  · intro hk b
    rw [conditionOn_EU_eq_twoStepEU, conditionOn_EU_eq_twoStepEU]
    exact (refrozen_isTwoStepChoice p hq hc hγ t k hk).1 b
  · intro hk
    rw [refrozen_askT_of_lt t k hk]
    exact (isOneStepChoice_pay p k (hγ k) hg).1

/-- **Theorem B, two-sided (the re-freezing dilemma)**: for `t < K` and `gain = V(1−q) − cq > 0`,
on one object: (i) the frozen prior's gap `𝔼[U | payAll] − 𝔼[U | refrozen t] = gain · ∑_{k≥t} γ_k
> 0` and `¬ NoStrictPrecommitAt (refrozen t) Ask_t`; (ii) the re-frozen prior's gap
`𝔼'[U | refrozen t] − 𝔼'[U | payAll] = c · ∑_{k≥t} γ_k > 0`; (iii) from `t` on the re-frozen
policy is the two-step rule at `{coin}` and the one-step rule of the re-frozen prior; before `t`
it is the one-step rule of the frozen prior. Every value is an `exAnteValue` of a positive-mass
policy; both directions are computed.
Source: bli-soto-a-2-017 (ii) (the concrete form of bli-soto-a-2-016 and of bli-soto-a-084's
dilemma); bli-soto-b-038 ("locks in"); [[bli-program-desiderata]] I10 Theorem B (tiling half);
[[bli-program-construction]] X7; [[bli-program]] §3.9 U9(6); mandate T4(d)
Kind: C
Fidelity: exact (finite horizon, one re-freeze day; the schedule form is the iteration)
Hyps: (a) `0 < q`, `0 < c`, `0 < γ_k`, `0 < gain`, `t < K`; does not use faith -/
theorem refreeze_dilemma (hq : 0 < p.q) (hc : 0 < p.c) (hg : 0 < gain p) (hγ : ∀ k, 0 < p.γ k)
    (t : ℕ) (ht : t < K) :
    ((scPrior p).exAnteValue payAll - (scPrior p).exAnteValue (refrozen t) =
        gain p * tailSum p.γ t ∧ 0 < gain p * tailSum p.γ t ∧
      ¬ NoStrictPrecommitAt (scPrior p) (refrozen t) (askT K ⟨t, ht⟩)) ∧
    ((conditionOn (scPrior p) (coinClass K) (coinClass_pos p hq)).exAnteValue (refrozen t) -
        (conditionOn (scPrior p) (coinClass K) (coinClass_pos p hq)).exAnteValue payAll =
        p.c * tailSum p.γ t ∧ 0 < p.c * tailSum p.γ t) ∧
    (∀ k : Fin K, t ≤ k.val →
      IsTwoStepChoice (scPrior p) {coin1 K} (askT K k) (refrozen t (askT K k)) ∧
      (conditionOn (scPrior p) (coinClass K) (coinClass_pos p hq)).IsOneStepChoice (askT K k)
        (refrozen t (askT K k))) ∧
    (∀ k : Fin K, k.val < t → (scPrior p).IsOneStepChoice (askT K k) (refrozen t (askT K k))) :=
  ⟨⟨frozen_gap p t, mul_pos hg (tailSum_pos p hγ t ht),
      refreeze_not_noStrictPrecommitAt p t ht hg hγ⟩,
    ⟨refrozen_gap p hq t, mul_pos hc (tailSum_pos p hγ t ht)⟩,
    fun k hk => ⟨(refrozen_isTwoStepChoice p hq hc hγ t k hk).1,
      (refrozen_isOneStepChoice_conditioned p hq hc hg hγ t k).1 hk⟩,
    fun k hk => (refrozen_isOneStepChoice_conditioned p hq hc hg hγ t k).2 hk⟩

/-! ## Dynamic stability iff the prior never updates (T4(e)) -/

/-- **A policy re-frozen at `Σ` from round `t` on**: pays at `Ask_k` for `k < t`, and at every
`Ask_k` with `k ≥ t` is a two-step choice at `Σ` (any tie-breaking). `refrozen t` is one for
`Σ = {coin}` (`isRefrozen_coin`), `payAll` is one for `Σ = ∅` (`isRefrozen_empty`).
Source: bli-soto-a-2-016 (the family `P_σ`); mandate T4(e) (the model class)
Kind: D
Fidelity: exact -/
def IsRefrozen (Sig : Finset ↥((iterIndex K).S 1)) (t : ℕ) (π : Policy (iterTables K) Bool) :
    Prop :=
  (∀ k : Fin K, k.val < t → π (askT K k) = true) ∧
    ∀ k : Fin K, t ≤ k.val → IsTwoStepChoice (scPrior p) Sig (askT K k) (π (askT K k))

/-- `refrozen t` is re-frozen at `{coin}` from `t` on.
Source: mandate T4(e)
Kind: N+
Fidelity: exact
Hyps: (a) `0 < q`, `0 < c`, `0 < γ_k` -/
theorem isRefrozen_coin (hq : 0 < p.q) (hc : 0 < p.c) (hγ : ∀ k, 0 < p.γ k) (t : ℕ) :
    IsRefrozen p {coin1 K} t (refrozen t) :=
  ⟨fun k hk => refrozen_askT_of_lt t k hk,
    fun k hk => (refrozen_isTwoStepChoice p hq hc hγ t k hk).1⟩

/-- `payAll` is re-frozen at `∅` from every `t` on (the two-step rule at `∅` is the one-step rule,
which pays).
Source: mandate T4(e) (`Σ = ∅`, `twoStepEU_empty`)
Kind: N+
Fidelity: exact
Hyps: (a) `0 < gain`, `0 < γ_k` -/
theorem isRefrozen_empty (hg : 0 < gain p) (hγ : ∀ k, 0 < p.γ k) (t : ℕ) :
    IsRefrozen p ∅ t payAll := by
  refine ⟨fun _ _ => rfl, fun k _ b => ?_⟩
  rw [twoStepEU_empty, twoStepEU_empty]
  exact (isOneStepChoice_pay p k (hγ k) hg).1 b

/-- **Dynamic stability iff the re-freeze changes no decision**: over the class `IsRefrozen Σ t`,
with `gain > 0`, a re-frozen policy has no strict preference for precommitment iff its two-step
decisions from `t` on agree with the one-step decision (= pay) at every round `k ≥ t`.
Source: bli-soto-b-034 D1 ("D1 holds iff `𝙿` never updates" — read as "iff the re-freeze changes
no one-step decision at a positive-stake round", ATTRIBUTION-UNVETTED); [[bli-program-desiderata]]
U7; mandate T4(e)
Kind: C (`noStrictPrecommit_iff_payOnAsk`)
Fidelity: variant: "never updates" rendered as "the re-freeze changes no one-step decision"
(disclosed)
Hyps: (a) `0 < gain`, `0 < γ_k`, `IsRefrozen Σ t π`; does not use faith -/
theorem stability_iff (hg : 0 < gain p) (hγ : ∀ k, 0 < p.γ k)
    (Sig : Finset ↥((iterIndex K).S 1)) (t : ℕ) (π : Policy (iterTables K) Bool)
    (hπ : IsRefrozen p Sig t π) :
    NoStrictPrecommit (scPrior p) π ↔ ∀ k : Fin K, t ≤ k.val → π (askT K k) = true := by
  rw [noStrictPrecommit_iff_payOnAsk p hg hγ]
  constructor
  · intro h k _; exact h k
  · intro h k
    by_cases hk : k.val < t
    · exact hπ.1 k hk
    · exact h k (not_lt.mp hk)

/-- **With `Σ = {coin}`, stability iff the re-freeze is empty**: a policy re-frozen on the coin
from `t` on has no strict preference for precommitment iff `K ≤ t` (no round is re-frozen).
Source: bli-soto-b-034 D1; bli-soto-a-2-016; mandate T4(e) ("with `Sig = {coin}` the right side is
`t = K`")
Kind: C
Fidelity: exact
Hyps: (a) `0 < q`, `0 < c`, `0 < gain`, `0 < γ_k`; does not use faith -/
theorem stability_coin_iff (hq : 0 < p.q) (hc : 0 < p.c) (hg : 0 < gain p) (hγ : ∀ k, 0 < p.γ k)
    (t : ℕ) (π : Policy (iterTables K) Bool) (hπ : IsRefrozen p {coin1 K} t π) :
    NoStrictPrecommit (scPrior p) π ↔ K ≤ t := by
  rw [stability_iff p hg hγ _ t π hπ]
  constructor
  · intro h
    by_contra hlt
    have hlt : t < K := Nat.lt_of_not_le hlt
    have h1 := h ⟨t, hlt⟩ (le_refl _)
    have h2 := hπ.2 ⟨t, hlt⟩ (le_refl _)
    rw [h1] at h2
    exact (isTwoStepChoice_refuse p ⟨t, hlt⟩ hq hc (hγ _)).2 h2
  · intro h k hk
    have := k.isLt
    omega

/-- **With `Σ = ∅`, every re-frozen policy is stable** (the re-freeze changes nothing).
Source: mandate T4(e) (`Σ = ∅`, `twoStepEU_empty`: the N− boundary where tiling holds)
Kind: C
Fidelity: exact
Hyps: (a) `0 < gain`, `0 < γ_k`; does not use faith -/
theorem stability_empty (hg : 0 < gain p) (hγ : ∀ k, 0 < p.γ k) (t : ℕ)
    (π : Policy (iterTables K) Bool) (hπ : IsRefrozen p ∅ t π) :
    NoStrictPrecommit (scPrior p) π := by
  rw [stability_iff p hg hγ _ t π hπ]
  intro k hk
  have h2 := hπ.2 k hk
  have h1 : (scPrior p).IsOneStepChoice (askT K k) (π (askT K k)) := by
    intro b
    have := h2 b
    rw [twoStepEU_empty, twoStepEU_empty] at this
    exact this
  by_contra hne
  have hf : π (askT K k) = false := by simpa using hne
  rw [hf] at h1
  exact (isOneStepChoice_pay p k (hγ k) hg).2 h1

/-! ## Self-trust (T8) -/

/-- **Self-trust of the frozen prior against its re-freezing on the coin** holds for `payAll`
(Kind `T`: it is prior-optimal), and its content on the re-frozen prior's one-step policy
`refrozen 0` (refuse everywhere) is the *same* strict gap as Theorem B's frozen side at `t = 0`:
self-trust of the frozen prior and the loss of tiling under re-freezing are one fact read from
two sides.
Source: bli-soto-a-016 (self-trust); bli-soto-a-073 (weak-without-strong has a tiling problem —
the informal form, ill-posed as the source says until the self-modification action is defined);
mandate T8
Kind: T + L
Fidelity: weaker: the alternative belief state is the re-freezing on the coin (finite shadow)
Hyps: (a) `0 < q`, `0 < c`, `0 ≤ gain`/`0 < gain`, `0 < γ_k`; does not use faith -/
theorem selfTrust_is_refreeze_gap (hq : 0 < p.q) (hc : 0 < p.c) (hg : 0 < gain p)
    (hγ : ∀ k, 0 < p.γ k) :
    SelfTrustAgainst (coinClass K) (coinClass_pos p hq) payAll ∧
      (conditionOn (scPrior p) (coinClass K) (coinClass_pos p hq)).IsOneStepPolicy (refrozen 0) ∧
      (scPrior p).exAnteValue payAll - (scPrior p).exAnteValue (refrozen 0) =
        gain p * tailSum p.γ 0 := by
  refine ⟨selfTrustAgainst_of_priorOptimalOnSupport _ _
      ((scPrior p).isPriorOptimalOnSupport_of_isPriorOptimal
        (priorOptimal_payAll p hg.le (fun k => (hγ k).le))),
    fun T => ?_, frozen_gap p 0⟩
  -- every table is some `st s`; at `Ask_k` the conditioned one-step choice is `refuse`; at the
  -- other tables every action is tied (the utility reads only the `Ask` points)
  obtain ⟨s, rfl⟩ := st_surjective K T
  rcases s with _ | ⟨b, k⟩
  · intro a'
    exact le_of_eq (conditionOn_EU_tied p _ (otherT K) (fun j => askT_ne_otherT j) a' _)
  · cases b
    · intro a'
      exact le_of_eq (conditionOn_EU_tied p _ (recT K k) (fun j => askT_ne_recT j k) a' _)
    · exact (refrozen_isOneStepChoice_conditioned p hq hc hg hγ 0 k).1 (Nat.zero_le _)

/-! ## The numeric instance (mandate T4 witness; [[plan]] rule 4: exact rationals) -/

/-- The instance `(c, V) = (10, 100)`, `q = 1/2`, `K = 3`, `w ≡ 1/3`, `γ ≡ 1`, `r₀ ≡ 0`.
Source: mandate T4 (witness); bli-soto-a-084 (`(−10, +100)`)
Kind: D
Fidelity: exact -/
def inst : Params 3 where
  q := 1 / 2
  hq0 := by norm_num
  hq1 := by norm_num
  w := fun _ => 1 / 3
  hw := fun _ => by norm_num
  hw1 := by rw [Fin.sum_univ_three]; norm_num
  c := 10
  V := 100
  γ := fun _ => 1
  r₀ := fun _ => 0

/-- `0 < q` on the instance.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma inst_hq : 0 < inst.q := by norm_num [inst]

/-- `gain = 45` on the instance; the threshold is the exact rational `10/11`, and `q = 1/2 < 10/11`.
Source: mandate §3.5 (numerics), T4 (witness)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem inst_gain : gain inst = 45 ∧ inst.V / (inst.V + inst.c) = 10 / 11 ∧ inst.q < 10 / 11 := by
  refine ⟨by unfold gain inst; norm_num, by norm_num [inst], by norm_num [inst]⟩

/-- The tail weights of the instance: `∑_{k ≥ 1} γ_k = 2`, `∑_{k ≥ 2} γ_k = 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem inst_tailSum : tailSum inst.γ 1 = 2 ∧ tailSum inst.γ 2 = 1 := by
  unfold tailSum inst
  simp only [Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two]
  norm_num

/-- **The verdict on the instance**: `EU Ask_j give − EU Ask_j refuse = 45` at every round.
Source: mandate T4 (witness)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem inst_verdict (j : Fin 3) :
    (scPrior inst).EU (askT 3 j) true - (scPrior inst).EU (askT 3 j) false = 45 := by
  rw [EU_diff, inst_gain.1]; norm_num [inst]

/-- **The dilemma on the instance**: re-freezing from round `1` on, the frozen prior's gap is
`90` and the re-frozen prior's gap is `20`; from round `2` on, `45` and `10`; and
`¬ NoStrictPrecommitAt (refrozen 1) Ask_1`. (The mandate's "`45` and `20`" do not occur at one
`t`: the frozen gap is `45` per re-frozen round, the re-frozen gap `10`.)
Source: mandate T4 (witness: "gap 45 in (d), 20 in the conditioned direction")
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem inst_dilemma :
    ((scPrior inst).exAnteValue payAll - (scPrior inst).exAnteValue (refrozen 1) = 90 ∧
      (scPrior inst).exAnteValue payAll - (scPrior inst).exAnteValue (refrozen 2) = 45) ∧
    ((conditionOn (scPrior inst) (coinClass 3) (coinClass_pos inst inst_hq)).exAnteValue
        (refrozen 1) -
      (conditionOn (scPrior inst) (coinClass 3) (coinClass_pos inst inst_hq)).exAnteValue payAll
        = 20 ∧
      (conditionOn (scPrior inst) (coinClass 3) (coinClass_pos inst inst_hq)).exAnteValue
        (refrozen 2) -
      (conditionOn (scPrior inst) (coinClass 3) (coinClass_pos inst inst_hq)).exAnteValue payAll
        = 10) ∧
    ¬ NoStrictPrecommitAt (scPrior inst) (refrozen 1) (askT 3 ⟨1, by norm_num⟩) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · rw [frozen_gap, inst_gain.1, inst_tailSum.1]; norm_num
  · rw [frozen_gap, inst_gain.1, inst_tailSum.2]; norm_num
  · rw [refrozen_gap inst inst_hq, inst_tailSum.1]; norm_num [inst]
  · rw [refrozen_gap inst inst_hq, inst_tailSum.2]; norm_num [inst]
  · exact refreeze_not_noStrictPrecommitAt inst 1 (by norm_num) (by rw [inst_gain.1]; norm_num)
      (fun _ => by norm_num [inst])

end SingleCoin

end Cleanroom.Bli.UdtBliTiling
