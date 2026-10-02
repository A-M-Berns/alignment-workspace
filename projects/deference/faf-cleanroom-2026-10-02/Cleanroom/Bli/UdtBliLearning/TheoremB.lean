import Cleanroom.Bli.UdtBliLearning.Defs
import Cleanroom.Bli.UdtBliLearning.TheoremA

/-!
# `udt-bli-learning` · TheoremB: the re-frozen policy weakly learns, does not strongly learn at the
frozen state, and does not tile — the finite instance of "weak-not-strong has a tiling problem" (T3)

**Scope: single coin, additive stakes, finite horizon `K`, the prior pays (`gain > 0`), the coin
true, decision day `0 < N`, a re-freezing schedule `t_0 = 0 < t_1 < …` with `N ≤ t_1 < K`.**

A **schedule** (`Schedule K N`) is a strictly increasing `t : ℕ → ℕ` with `t 0 = 0` and
`N ≤ t 1 < K`; the agent acting on `[t_j, t_{j+1})` by one-step UDT over `Q_{t_j}` is, on the
model, `udt-bli-tiling`'s `refrozen (t 1)` (pay before `t 1`, refuse from `t 1` on): every state
`Q_{t_j}` with `j ≥ 1` is the decided state, whose one-step rule is `refuse`. The schedule's
learning rate is `schedF s n := min {t_j | n ≤ t_j}` (`Nat.find`), with `n ≤ schedF s n`,
`schedF s 0 = 0`, `t 1 ≤ schedF s n` for `0 < n`, monotone.

* `refrozen_weakLearns`: the re-frozen policy weakly learns with rate `schedF` (grade (a), by
  inspection through `Defs.lean`'s `weakLearns_iff`).
* `refrozen_not_strongLearnsAt_zero`: it does not strongly learn at the frozen state `Q_0 = P`
  (at `Ask_{t 1}` it refuses, `P` pays).
* `refrozen_weak_not_strong_not_tiles`: the package with the imported tiling failure
  `refreeze_not_noStrictPrecommitAt` and the re-frozen prior's own gap `refrozen_gap` — the
  *instance* of bli-soto-a-073's "a construction which gets the weak interpretation and not the
  strong one seems like it should have tiling concerns", never the general theorem (the thread's
  reply calls "give it an action [to overthrow `P`]" unclear: "whether it's present and observable
  in the decision tree from the start, or only introduced once `Q_n` is in control").
* N−: `strongLearnsAt_payAll_early` — a re-freeze on a state before `N` changes nothing (the
  early states' one-step rule is `payAll`).
* **Schedules are inhabited, and Theorem B fires on the numeric instance** (repair round 2, audit
  r2 adversarial N1 — a `∀ s : Schedule K N` theorem is not its own witness): `schedOfPos` (the
  generic schedule `t 0 = 0`, `t j = N + (j − 1)` for every `0 < N < K`), `instSched` (`t = id` on
  `udt-bli-tiling`'s `inst`, `K = 3`, `N = 1`) and `inst_theoremB` (N+: `refrozen 1` weakly learns
  with rate `schedF instSched`, does not strongly learn at `Q_0`, is not endorsed by the frozen
  prior at `Ask_1`, the re-frozen prior's gap is `20` and the frozen prior's gap is `90`).

Sources: bli-soto-a-2-017 (i)–(ii) (the schedule `P^{(k)}` refusing from `t_k`), bli-soto-a-073
(`soto-email-thread-2023.md` ll. 231–290), bli-soto-b-013 (PDF 15: the hard-coded "after `f(n)`
use `Q_n`" gets the weak reading); [[bli-program-desiderata]] I10 Theorem B; mandate T3 (core).
-/

set_option autoImplicit false

namespace Cleanroom.Bli.UdtBliLearning

open Cleanroom.Bli.BliFinite Cleanroom.Bli.UdtBliCore Cleanroom.Bli.UdtBliSist
  Cleanroom.Bli.UdtBliTiling Finset
open Cleanroom.Bli.UdtBliSist.Iter
open Cleanroom.Bli.UdtBliTiling.SingleCoin

/-! ## Schedules -/

/-- **A re-freezing schedule**: strictly increasing re-freeze days `t_0 = 0 < t_1 < …` with the
first re-freeze after the coin is decided (`N ≤ t 1`) and within the horizon (`t 1 < K`).
Source: bli-soto-a-2-017 (i) ("re-freezing at `t_1 < t_2 < …`"); mandate T3
Kind: D
Fidelity: exact (finite horizon: only `t 1` acts within `K` when `t 2 ≥ K`; the later
re-freezes change nothing on the model, all decided states agreeing) -/
structure Schedule (K N : ℕ) where
  /-- The re-freeze days. -/
  t : ℕ → ℕ
  /-- Strictly increasing. -/
  strictMono : StrictMono t
  /-- `t 0 = 0`: the first state is the frozen prior. -/
  t0 : t 0 = 0
  /-- The first re-freeze is on or after the decision day. -/
  hN : N ≤ t 1
  /-- The first re-freeze is within the horizon. -/
  hK : t 1 < K

variable {K N : ℕ}

/-- Some re-freeze day is at or after `n` (a strictly increasing `ℕ → ℕ` is unbounded).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma Schedule.exists_le (s : Schedule K N) (n : ℕ) : ∃ j, n ≤ s.t j :=
  ⟨n, s.strictMono.id_le n⟩

/-- **The schedule's learning rate** `schedF s n := min {t_j | n ≤ t_j}`: the first re-freeze day
at or after `n`.
Source: [[bli-program-desiderata]] I10 Theorem B ("weak `f`-learning with `f(n) = min{t_k ≥ n}`");
bli-soto-a-2-017 (i); mandate T3
Kind: D
Fidelity: exact -/
def schedF (s : Schedule K N) (n : ℕ) : ℕ := s.t (Nat.find (s.exists_le n))

/-- `n ≤ schedF s n`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma le_schedF (s : Schedule K N) (n : ℕ) : n ≤ schedF s n := Nat.find_spec (s.exists_le n)

/-- `schedF s n` is the least re-freeze day at or after `n`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma schedF_le (s : Schedule K N) {n j : ℕ} (h : n ≤ s.t j) : schedF s n ≤ s.t j :=
  s.strictMono.monotone (Nat.find_min' (s.exists_le n) h)

/-- `schedF s n` is a re-freeze day.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma schedF_mem (s : Schedule K N) (n : ℕ) : ∃ j, schedF s n = s.t j := ⟨_, rfl⟩

/-- `schedF s 0 = 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma schedF_zero (s : Schedule K N) : schedF s 0 = 0 := by
  unfold schedF
  have : Nat.find (s.exists_le 0) = 0 := Nat.find_eq_zero (s.exists_le 0) |>.mpr (Nat.zero_le _)
  rw [this, s.t0]

/-- For `0 < n`, `t 1 ≤ schedF s n`: the first re-freeze day at or after a positive `n` is at
least `t 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma t1_le_schedF (s : Schedule K N) {n : ℕ} (hn : 0 < n) : s.t 1 ≤ schedF s n := by
  unfold schedF
  apply s.strictMono.monotone
  have : 0 < Nat.find (s.exists_le n) := by
    rw [Nat.find_pos]
    rw [s.t0]
    exact not_le.mpr hn
  exact this

/-- `schedF s` is monotone.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma schedF_mono (s : Schedule K N) : Monotone (schedF s) := by
  intro n n' h
  unfold schedF
  apply s.strictMono.monotone
  exact Nat.find_mono (fun j (hj : n' ≤ s.t j) => h.trans hj)

/-- **The generic schedule** for `0 < N < K`: `t 0 = 0`, `t j = N + (j − 1)` for `j ≥ 1` (so
`t 1 = N`, strictly increasing). `Schedule K N` is inhabited exactly when `0 < N < K`
(`schedule_nonempty`).
Source: mandate T3; audit r2 adversarial N1 (probe `ScheduleWitness`)
Kind: D
Fidelity: n/a -/
def schedOfPos (hN : 0 < N) (hK : N < K) : Schedule K N where
  t := fun j => if j = 0 then 0 else N + (j - 1)
  strictMono := by
    intro a b hab
    simp only
    by_cases ha : a = 0
    · subst ha
      have hb : b ≠ 0 := by omega
      simp only [if_true, if_neg hb]
      omega
    · have hb : b ≠ 0 := by omega
      simp only [if_neg ha, if_neg hb]
      omega
  t0 := by simp
  hN := by simp
  hK := by simpa using hK

/-- `Schedule K N` is inhabited whenever `0 < N < K` — the hypothesis package of Theorem B's
learning half is satisfiable.
Source: mandate T3; audit r2 adversarial N1
Kind: N+
Fidelity: n/a
Hyps: (a) `0 < N`, `N < K` -/
theorem schedule_nonempty (hN : 0 < N) (hK : N < K) : Nonempty (Schedule K N) :=
  ⟨schedOfPos hN hK⟩

/-- **The numeric schedule** on `udt-bli-tiling`'s `inst` (`K = 3`, `N = 1`): `t = id`, so
`t 1 = 1`.
Source: mandate T3; audit r2 adversarial N1
Kind: D
Fidelity: n/a -/
def instSched : Schedule 3 1 where
  t := id
  strictMono := strictMono_id
  t0 := rfl
  hN := le_rfl
  hK := by decide

/-! ## Theorem B, the learning half -/

variable (p : Params K) (hb : 0 < stateClassMass (scPrior p) (coinClassOf K true))

/-- **The re-frozen policy weakly learns** with the schedule's rate: for every `n`, from round
`schedF s n` on, every action of `refrozen (t 1)` is a one-step choice of some `Q_x`, `x ≥ n`
(for `n ≥ N`: of `Q_n` itself, which refuses; for `n < N`: of `Q_n` where it pays and of `Q_N`
where it refuses).
Source: bli-soto-a-2-017 (i) ("has weak `f`-learning with `f(n) = min{t_k ≥ n}`, by
inspection"); bli-soto-b-013 (the hard-coded construction "gets the weak one");
[[bli-program-desiderata]] I10 Theorem B; mandate T3
Kind: C (`weakLearns_iff`, `actsAs_true_of_le`, `t1_le_schedF`)
Fidelity: exact
Hyps: (a) `0 < q`, `0 < c`, `0 < γ`, `0 < gain`, `0 < N`, the schedule; does not use faith -/
theorem refrozen_weakLearns (hq : 0 < p.q) (hc : 0 < p.c) (hg : 0 < gain p)
    (hγ : ∀ k, 0 < p.γ k) (hN : 0 < N) (s : Schedule K N) :
    WeakLearns (beliefState p true N hb) (realized true) (schedF s) (refrozen (s.t 1)) := by
  rw [weakLearns_iff p hb (schedF s) hq hc hg hγ]
  intro n hn k hk
  rw [actsAs_true_of_le p hq hc hγ hb hn]
  exact refrozen_askT_of_le (s.t 1) k ((t1_le_schedF s (hN.trans_le hn)).trans hk)

/-- **The re-frozen policy does not strongly learn at the frozen state `Q_0 = P`**: at
`Ask_{t 1}` (a round `≥ schedF s 0 = 0`) it refuses while `P` uniquely pays.
Source: bli-soto-a-073 ("your construction establishes the weak property rather than the strong
one"); bli-soto-a-2-017 (ii); mandate T3
Kind: C (`strongLearnsAt_early_iff`, `schedF_zero`)
Fidelity: exact
Hyps: (a) `0 < gain`, `0 < γ`, `0 < N`, the schedule; does not use faith -/
theorem refrozen_not_strongLearnsAt_zero (hg : 0 < gain p) (hγ : ∀ k, 0 < p.γ k) (hN : 0 < N)
    (s : Schedule K N) :
    ¬ StrongLearnsAt (beliefState p true N hb) (realized true) (schedF s) (refrozen (s.t 1)) 0 := by
  rw [strongLearnsAt_early_iff p hb (schedF s) hg hγ hN]
  intro h
  have := h ⟨s.t 1, s.hK⟩ (by rw [schedF_zero]; exact Nat.zero_le _)
  rw [refrozen_askT_of_le (s.t 1) ⟨s.t 1, s.hK⟩ le_rfl] at this
  exact Bool.noConfusion this

/-- **Theorem B, the learning half packaged with the imported tiling failure (the instance of
"weak-not-strong does not tile")**: on the model, the schedule's re-frozen policy (a) weakly
learns, (b) does not strongly learn at the frozen state, (c) is strictly beaten under the frozen
prior by the one-point precommitment "pay at `Ask_{t 1}`" (`¬ NoStrictPrecommitAt`) — **the
overthrow**: the thread's scenario with `n = 0`, where `Q_0` (the un-edited frozen prior) does not
endorse the schedule's update and strictly prefers the one-point self-modification that undoes it
— and (d) the re-frozen prior itself strictly prefers the re-frozen policy to `payAll` by
`c · ∑_{k ≥ t 1} γ_k` (`udt-bli-tiling`'s `refrozen_gap`) — the decided state's *endorsement* of
the re-freeze, the other side of the dilemma. This is the single-coin *instance*; the general
"weak-not-strong has a tiling problem" is not stated (its author left "give it an action"
undefined).
Source: [[bli-program-desiderata]] I10 Theorem B (primary for (c)/(d)); bli-soto-a-073 ("a
construction which gets the weak interpretation and not the strong one seems like it should have
tiling concerns … `Q_n` should prefer self-modifications which overthrow `P`", the `n = 0`
instance reading); bli-soto-a-2-017 (ii); mandate T3
Kind: C (`refrozen_weakLearns`, `refrozen_not_strongLearnsAt_zero`,
`refreeze_not_noStrictPrecommitAt`, `refrozen_gap`)
Fidelity: weaker: the finite single-coin instance of the informal general claim; the "self-
modification action" is the one-point precommitment of `NoStrictPrecommitAt`
Hyps: (a) `0 < q`, `0 < c`, `0 < γ`, `0 < gain`, `0 < N`, the schedule; does not use faith -/
theorem refrozen_weak_not_strong_not_tiles (hq : 0 < p.q) (hc : 0 < p.c) (hg : 0 < gain p)
    (hγ : ∀ k, 0 < p.γ k) (hN : 0 < N) (s : Schedule K N) :
    WeakLearns (beliefState p true N hb) (realized true) (schedF s) (refrozen (s.t 1)) ∧
    ¬ StrongLearnsAt (beliefState p true N hb) (realized true) (schedF s) (refrozen (s.t 1)) 0 ∧
    ¬ NoStrictPrecommitAt (scPrior p) (refrozen (s.t 1)) (askT K ⟨s.t 1, s.hK⟩) ∧
    ((conditionOn (scPrior p) (coinClass K) (coinClass_pos p hq)).exAnteValue (refrozen (s.t 1)) -
      (conditionOn (scPrior p) (coinClass K) (coinClass_pos p hq)).exAnteValue payAll =
        p.c * tailSum p.γ (s.t 1) ∧ 0 < p.c * tailSum p.γ (s.t 1)) :=
  ⟨refrozen_weakLearns p hb hq hc hg hγ hN s, refrozen_not_strongLearnsAt_zero p hb hg hγ hN s,
    refreeze_not_noStrictPrecommitAt p (s.t 1) s.hK hg hγ,
    refrozen_gap p hq (s.t 1), mul_pos hc (tailSum_pos p hγ (s.t 1) s.hK)⟩

/-- **The schedule's agent, in Lean**: `refrozen (t 1)` acts as the decided state `Q_N` at every
round `k ≥ t 1` and as the frozen state `Q_0` at every round `k < t 1` — the identification "the
agent acting on `[t_j, t_{j+1})` by one-step UDT over `Q_{t_j}` is `refrozen (t 1)`" as a theorem
rather than a docstring (for `j ≥ 1` every `Q_{t_j}` is the decided state).
Source: bli-soto-a-2-017 (i); [[bli-program-desiderata]] I10 Theorem B; mandate T3; audit r1
fidelity N8
Kind: C (`actsAs_true_of_le`, `actsAs_true_of_lt`, `refrozen_askT_of_le`, `refrozen_askT_of_lt`)
Fidelity: exact
Hyps: (a) `0 < q`, `0 < c`, `0 < γ`, `0 < gain`, `0 < N`, the schedule; does not use faith -/
theorem refrozen_actsAs_schedule (hq : 0 < p.q) (hc : 0 < p.c) (hg : 0 < gain p)
    (hγ : ∀ k, 0 < p.γ k) (hN : 0 < N) (s : Schedule K N) (k : Fin K) :
    (s.t 1 ≤ k.val → ActsAs (beliefState p true N hb) (realized true) (refrozen (s.t 1)) N k) ∧
    (k.val < s.t 1 → ActsAs (beliefState p true N hb) (realized true) (refrozen (s.t 1)) 0 k) :=
  ⟨fun hk => (actsAs_true_of_le p hq hc hγ hb le_rfl _ k).mpr (refrozen_askT_of_le _ k hk),
   fun hk => (actsAs_true_of_lt p hg hγ hb hN _ k).mpr (refrozen_askT_of_lt _ k hk)⟩

/-- **N−: `refuseAll` weakly learns with every rate.** On this model `WeakLearns f π` is "`π`
refuses at every round `k ≥ f n` for every `n ≥ N`" (`weakLearns_iff`), so a policy that never
acts as the frozen prior anywhere weakly learns for every `f`; `refrozen_weakLearns` is the
instance of that characterization at `π = refrozen (t 1)`, `f = schedF s`, and the schedule's
`t 2, t 3, …` are idle. This is how much content "weak learning" retains on a two-state model
(F4).
Source: mandate T3; audit r1 adversarial N2 (probe `WeakIsTail`)
Kind: N−
Fidelity: exact
Hyps: (a) `0 < q`, `0 < c`, `0 < γ`, `0 < gain`; does not use faith -/
theorem refuseAll_weakLearns_any_rate (hq : 0 < p.q) (hc : 0 < p.c) (hg : 0 < gain p)
    (hγ : ∀ k, 0 < p.γ k) (f : ℕ → ℕ) :
    WeakLearns (beliefState p true N hb) (realized true) f refuseAll := by
  rw [weakLearns_iff p hb f hq hc hg hγ]
  intro n hn k _
  exact (actsAs_true_of_le p hq hc hγ hb hn refuseAll k).mpr rfl

/-- **N−: a re-freeze on a state before the decision day changes nothing** — at every early state
`n < N` the one-step rule is `payAll`, which strongly learns there (for any rate), so re-freezing
on `Q_n` with `n < N` reproduces the frozen prior's policy.
Source: mandate T3 (N− lemma: "a re-freeze before `N` changes nothing")
Kind: N−
Fidelity: exact
Hyps: (a) `0 < gain`, `0 < γ`, `n < N`; does not use faith -/
theorem strongLearnsAt_payAll_early (hg : 0 < gain p) (hγ : ∀ k, 0 < p.γ k) (f : ℕ → ℕ) {n : ℕ}
    (hn : n < N) :
    StrongLearnsAt (beliefState p true N hb) (realized true) f payAll n := by
  rw [strongLearnsAt_early_iff p hb f hg hγ hn]
  intro k _
  rfl

/-- **Theorem B's learning half on the numeric instance (N+)**: with the schedule `t = id` on
`inst` (`K = 3`, `N = 1`), the re-frozen policy `refrozen 1` weakly learns with rate `schedF`,
does not strongly learn at the frozen state, is strictly beaten under the frozen prior by the
one-point precommitment at `Ask_1`, the re-frozen prior's gap is `20`, and the frozen prior's gap
against `payAll` is `90` (`inst_dilemma`). The full hypothesis package of
`refrozen_weak_not_strong_not_tiles` is inhabited and its conclusion is numerically exercised.
Source: [[bli-program-desiderata]] I10 Theorem B; mandate T3 (N+); audit r2 adversarial N1 (probe
`ScheduleWitness`)
Kind: N+
Fidelity: exact (the instance)
Hyps: (a) none -/
theorem inst_theoremB :
    WeakLearns (beliefState inst true 1 (coinClass_pos inst inst_hq)) (realized true)
      (schedF instSched) (refrozen 1) ∧
    ¬ StrongLearnsAt (beliefState inst true 1 (coinClass_pos inst inst_hq)) (realized true)
      (schedF instSched) (refrozen 1) 0 ∧
    ¬ NoStrictPrecommitAt (scPrior inst) (refrozen 1) (askT 3 ⟨1, by norm_num⟩) ∧
    ((conditionOn (scPrior inst) (coinClass 3) (coinClass_pos inst inst_hq)).exAnteValue
        (refrozen 1) -
      (conditionOn (scPrior inst) (coinClass 3) (coinClass_pos inst inst_hq)).exAnteValue payAll
        = 20) ∧
    (scPrior inst).exAnteValue payAll - (scPrior inst).exAnteValue (refrozen 1) = 90 := by
  obtain ⟨h1, h2, h3, _, _⟩ := refrozen_weak_not_strong_not_tiles inst
    (coinClass_pos inst inst_hq) inst_hq inst_hc inst_hg inst_hγ (by norm_num) instSched
  exact ⟨h1, h2, h3, inst_dilemma.2.1.1, inst_dilemma.1.1⟩

end Cleanroom.Bli.UdtBliLearning
