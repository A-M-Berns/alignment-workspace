import Cleanroom.Li.TtLadder.WitnessesLog
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Log

/-!
# `tt-ladder`: schedules — the greedy lemma, the separating profile, the staircase

Target 7 of [[tt-ladder-mandate]], over `WindowDisjoint d := StrictMono d ∧ ∀ k, 2 ^ d k ≤ d (k+1)`
(v3 §3's shape, no computability clause).

* **Greedy lemma**: every infinite `S ⊆ ℕ` contains the image of a window-disjoint schedule.
  Corollary: if `∑_k w (d k) < ∞` for *every* window-disjoint `d` then `w → 0` (for `w ≥ 0`).
  Non-vacuity of the class: the tower `1, 2, 4, 16, 65536, …` is window-disjoint.
* **root-fa-015**: the profile `min 1 (1/log (n+2))` (W1's gate) is not summable, yet its sum
  along every window-disjoint schedule converges — "finite on every window-disjoint schedule"
  (v3 Theorem 1's conclusion) does not give "finite over all days" (the note's box).
* **The staircase refutes root-fa-2-003 (ii)'s converse**: `w n = 1/(k+1)` on `[tower k, tower (k+1))`
  tends to `0`, yet `∑_k w (tower k) = ∑ 1/(k+1) = ∞`. So "`∑_k w_{d_k} < ∞` for all
  window-disjoint `d` ⟺ `w_n → 0`" holds in one direction only.
* **Growth**: a window-disjoint schedule dominates the tower, `tower k ≤ d (k+1)`, and
  `d k ≤ Nat.log 2 (d (k+1))` — an output with `≥ d_k` bits; the "e.c. in the index" reading
  of v3's definition empties the class (finding, [[tt-ladder-findings]]).

Over `ℕ → ℕ` and real sequences; nothing here is a theorem about inductors, and FAF's
`DeferralFunction` is deliberately not instantiated here (see the findings).
-/

namespace Cleanroom.Li.TtLadder

open LogicalInduction Filter Topology
open Cleanroom.Found.LiAsympCalc

/-! ## The tower -/

/-- The tower `tower 0 = 1`, `tower (k+1) = 2 ^ tower k`.
Source: [[tt-ladder-mandate]] target 7; root-fa-2-003 (the "iterated exponentials")
Kind: D
Fidelity: exact
Hyps: n/a -/
def tower : ℕ → ℕ
  | 0 => 1
  | k + 1 => 2 ^ tower k

/-- `k + 1 ≤ tower k`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem succ_le_tower : ∀ k, k + 1 ≤ tower k
  | 0 => le_rfl
  | k + 1 => by
    show k + 2 ≤ 2 ^ tower k
    have h1 := succ_le_tower k
    have h2 : k + 1 < 2 ^ (k + 1) := Nat.lt_two_pow_self
    have h3 : 2 ^ (k + 1) ≤ 2 ^ tower k := Nat.pow_le_pow_right two_pos h1
    omega

/-- The tower is strictly increasing.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem tower_strictMono : StrictMono tower :=
  strictMono_nat_of_lt_succ (fun k => show tower k < 2 ^ tower k from Nat.lt_two_pow_self)

/-- **The class is non-empty**: the tower is window-disjoint (the check root-fa-2-003 asks for
once the deferral-function reading replaces "e.c. in the index").
Source: root-fa-2-003 (flag: "an N+-style check that the schedule class is non-empty")
Kind: N+
Fidelity: n/a
Hyps: n/a -/
theorem windowDisjoint_tower : WindowDisjoint tower :=
  ⟨tower_strictMono, fun k => show 2 ^ tower k ≤ 2 ^ tower k from le_rfl⟩

/-! ## The greedy lemma -/

/-- The greedy window-disjoint schedule inside an infinite set: each term is some element of
`S` above `2 ^ (previous term)` (classical choice).
Source: root-fa-2-003 (ii) ("greedy choice")
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def greedy (S : Set ℕ) (hS : S.Infinite) : ℕ → ℕ
  | 0 => Classical.choose (hS.exists_gt 0)
  | k + 1 => Classical.choose (hS.exists_gt (2 ^ greedy S hS k))

/-- Every term of the greedy schedule lies in `S`.
Source: root-fa-2-003 (ii)
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem greedy_mem (S : Set ℕ) (hS : S.Infinite) : ∀ k, greedy S hS k ∈ S
  | 0 => (Classical.choose_spec (hS.exists_gt 0)).1
  | k + 1 => (Classical.choose_spec (hS.exists_gt (2 ^ greedy S hS k))).1

/-- `2 ^ greedy k < greedy (k+1)`.
Source: root-fa-2-003 (ii)
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem greedy_succ_gt (S : Set ℕ) (hS : S.Infinite) (k : ℕ) :
    2 ^ greedy S hS k < greedy S hS (k + 1) :=
  (Classical.choose_spec (hS.exists_gt (2 ^ greedy S hS k))).2

/-- **The greedy lemma**: every infinite `S ⊆ ℕ` contains the image of a window-disjoint
schedule.
Source: root-fa-2-003 (ii) ("for every infinite `S` there is a strictly increasing `d` with `d_{k+1} ≥ 2^{d_k}` and `image(d) ⊆ S`")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem exists_windowDisjoint_subset {S : Set ℕ} (hS : S.Infinite) :
    ∃ d : ℕ → ℕ, WindowDisjoint d ∧ ∀ k, d k ∈ S :=
  ⟨greedy S hS,
    ⟨strictMono_nat_of_lt_succ (fun k => lt_trans Nat.lt_two_pow_self (greedy_succ_gt S hS k)),
      fun k => (greedy_succ_gt S hS k).le⟩,
    greedy_mem S hS⟩

/-- **Greedy corollary** (root-fa-2-003 (ii), `⟹`): if a nonnegative profile is summable along
*every* window-disjoint schedule, it tends to `0` — otherwise `w ≥ θ` on an infinite set, and
the greedy schedule inside it has a divergent subsum.
Source: root-fa-2-003 (ii) (the sound direction of the claimed equivalence)
Kind: P
Fidelity: exact (no upper bound on `w` needed)
Hyps: (a) none -/
theorem tendsto_zero_of_forall_windowDisjoint_summable {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n)
    (h : ∀ d : ℕ → ℕ, WindowDisjoint d → Summable (w ∘ d)) : Tendsto w atTop (𝓝 0) := by
  rw [tendsto_order]
  refine ⟨fun b hb => Eventually.of_forall (fun n => lt_of_lt_of_le hb (hw n)), ?_⟩
  intro θ hθ
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  have hinf : {n | θ ≤ w n}.Infinite :=
    Nat.frequently_atTop_iff_infinite.1 (hcon.mono (fun n hn => not_lt.1 hn))
  obtain ⟨d, hd, hdS⟩ := exists_windowDisjoint_subset hinf
  obtain ⟨N, hN⟩ := eventually_atTop.1 (summable_eventually_lt (h d hd) hθ)
  have h1 := hN N le_rfl
  have h2 : θ ≤ w (d N) := hdS N
  simp only [Function.comp] at h1
  linarith

/-! ## root-fa-015: the separating profile -/

/-- The profile `min 1 (1/log (n+2))` — W1's gate, `[0,1]`-valued.
Source: root-fa-015 (`w_n = 1/log(n+2)`, capped at `1` to stay in `[0,1]`); [[fa-positive-results-corrected-v2]] §5.6 l.201
Kind: D
Fidelity: variant: capped at `1`
Hyps: n/a -/
noncomputable def logProfile (n : ℕ) : ℝ := min 1 (1 / Real.log ((n : ℝ) + 2))

/-- `logProfile n ∈ [0,1]`.
Source: root-fa-015
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem logProfile_mem_Icc (n : ℕ) : logProfile n ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_min zero_le_one (div_nonneg zero_le_one (log_add_two_pos n).le), min_le_left _ _⟩

/-- `logProfile` is W1's gate.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem logProfile_eq_gateSeq_w1 (n : ℕ) : logProfile n = gateSeq (1/2) (1/10) w1Quote n :=
  (gateSeq_w1Quote n).symm

/-- **root-fa-015, divergence**: `∑ logProfile = ∞`.
Source: root-fa-015
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem not_summable_logProfile : ¬ Summable logProfile :=
  not_summable_of_one_div_succ_le one_pos
    (fun n => by rw [logProfile_eq_gateSeq_w1]; exact gateSeq_w1Quote_ge n)

/-- A window-disjoint schedule satisfies `k ≤ d k`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem WindowDisjoint.id_le {d : ℕ → ℕ} (hd : WindowDisjoint d) (k : ℕ) : k ≤ d k :=
  hd.1.id_le k

/-- A window-disjoint schedule satisfies `2 ^ k ≤ d (k+1)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem WindowDisjoint.two_pow_le {d : ℕ → ℕ} (hd : WindowDisjoint d) (k : ℕ) :
    2 ^ k ≤ d (k + 1) :=
  le_trans (Nat.pow_le_pow_right two_pos (hd.id_le k)) (hd.2 k)

/-- **root-fa-015, the schedule sums**: along every window-disjoint `d`, `∑_k logProfile (d k)`
converges — `logProfile (d (k+2)) ≤ 1/(d (k+1) · log 2) ≤ (1/log 2) · (1/2)^k`, geometric.
Source: root-fa-015; [[fa-positive-results-corrected-v2]] §5.6 l.201
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem summable_logProfile_comp {d : ℕ → ℕ} (hd : WindowDisjoint d) :
    Summable (logProfile ∘ d) := by
  rw [← summable_nat_add_iff 2]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hgeom : Summable (fun k : ℕ => (1 / Real.log 2) * (1/2 : ℝ) ^ k) :=
    summable_geometric_two.mul_left _
  refine hgeom.of_nonneg_of_le (fun k => (logProfile_mem_Icc _).1) (fun k => ?_)
  simp only [Function.comp]
  have hm : 2 ^ k ≤ d (k + 1) := hd.two_pow_le k
  have hd2 : 2 ^ d (k + 1) ≤ d (k + 2) := hd.2 (k + 1)
  have hd2R : (2 : ℝ) ^ d (k + 1) ≤ (d (k + 2) : ℝ) + 2 := by
    have : ((2 ^ d (k + 1) : ℕ) : ℝ) ≤ (d (k + 2) : ℝ) := by exact_mod_cast hd2
    push_cast at this
    linarith
  have hlogle : (d (k + 1) : ℝ) * Real.log 2 ≤ Real.log ((d (k + 2) : ℝ) + 2) := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) hd2R
  have hmR : (2 : ℝ) ^ k ≤ (d (k + 1) : ℝ) := by exact_mod_cast hm
  have hpos : (0 : ℝ) < (2 : ℝ) ^ k * Real.log 2 := by positivity
  calc logProfile (d (k + 2)) ≤ 1 / Real.log ((d (k + 2) : ℝ) + 2) := min_le_right _ _
    _ ≤ 1 / ((2 : ℝ) ^ k * Real.log 2) :=
        one_div_le_one_div_of_le hpos (le_trans (mul_le_mul_of_nonneg_right hmR hlog2.le) hlogle)
    _ = (1 / Real.log 2) * (1/2 : ℝ) ^ k := by
        rw [one_div_pow]
        field_simp

/-- **root-fa-015** (confirmation, not refutation): a `[0,1]`-valued profile whose total sum
diverges while every window-disjoint subsum converges. "Finite on every window-disjoint
schedule" does not give "finite over all days".
Source: root-fa-015; [[fa-positive-results-corrected-v2]] §5.6 l.201 (states the separation correctly)
Kind: N+
Fidelity: variant: capped profile
Hyps: n/a -/
theorem separating_profile :
    ∃ w : ℕ → ℝ, (∀ n, w n ∈ Set.Icc (0 : ℝ) 1) ∧ ¬ Summable w ∧
      ∀ d : ℕ → ℕ, WindowDisjoint d → Summable (w ∘ d) :=
  ⟨logProfile, logProfile_mem_Icc, not_summable_logProfile, fun _ hd => summable_logProfile_comp hd⟩

/-! ## The staircase: root-fa-2-003 (ii)'s converse is false -/

/-- The stair index: the largest `k ≤ n` with `tower k ≤ n`.
Source: [[tt-ladder-mandate]] target 7 (the staircase)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def stairIdx (n : ℕ) : ℕ := Nat.findGreatest (fun k => tower k ≤ n) n

/-- The staircase profile `1/(stairIdx n + 1)`: `1/(k+1)` on `[tower k, tower (k+1))`.
Source: [[tt-ladder-mandate]] target 7 (the staircase)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def staircase (n : ℕ) : ℝ := 1 / ((stairIdx n : ℝ) + 1)

/-- `stairIdx (tower k) = k`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem stairIdx_tower (k : ℕ) : stairIdx (tower k) = k := by
  unfold stairIdx
  rw [Nat.findGreatest_eq_iff]
  refine ⟨(Nat.le_succ k).trans (succ_le_tower k), fun _ => le_rfl, fun n hn _ hle => ?_⟩
  exact absurd hle (not_le.2 (tower_strictMono hn))

/-- `tower K ≤ n` gives `K ≤ stairIdx n`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem le_stairIdx {K n : ℕ} (h : tower K ≤ n) : K ≤ stairIdx n :=
  Nat.le_findGreatest (((Nat.le_succ K).trans (succ_le_tower K)).trans h) h

/-- `staircase n ∈ [0,1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem staircase_mem_Icc (n : ℕ) : staircase n ∈ Set.Icc (0 : ℝ) 1 := by
  unfold staircase
  constructor
  · positivity
  · rw [div_le_one (by positivity)]
    linarith [Nat.cast_nonneg (α := ℝ) (stairIdx n)]

/-- **The staircase tends to `0`**.
Source: [[tt-ladder-mandate]] target 7
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem tendsto_staircase : Tendsto staircase atTop (𝓝 0) := by
  rw [tendsto_order]
  refine ⟨fun b hb => Eventually.of_forall (fun n => lt_of_lt_of_le hb (staircase_mem_Icc n).1),
    ?_⟩
  intro θ hθ
  obtain ⟨K, hK⟩ := exists_nat_one_div_lt hθ
  filter_upwards [eventually_ge_atTop (tower K)] with n hn
  have hKn : K ≤ stairIdx n := le_stairIdx hn
  unfold staircase
  calc 1 / ((stairIdx n : ℝ) + 1) ≤ 1 / ((K : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hKn)
    _ < θ := hK

/-- **The staircase diverges along the tower**: `staircase (tower k) = 1/(k+1)`.
Source: [[tt-ladder-mandate]] target 7
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem not_summable_staircase_comp_tower : ¬ Summable (staircase ∘ tower) :=
  not_summable_of_one_div_succ_le one_pos (fun k => by
    simp only [Function.comp, staircase, stairIdx_tower]; exact le_rfl)

/-- **Refutation of root-fa-2-003 (ii)'s converse**: it is *not* the case that every
`[0,1]`-valued `w → 0` is summable along every window-disjoint schedule — the staircase tends
to `0` and diverges along the tower. With `tendsto_zero_of_forall_windowDisjoint_summable`,
the three grades `∑_n w_n < ∞ ⟹ (∀ window-disjoint d, ∑_k w_{d_k} < ∞) ⟹ w_n → 0` are each
strict (`separating_profile` for the first, this for the second). Reading of the inventory's
sentence: `(∀ d, WindowDisjoint d → Summable (w ∘ d)) ↔ Tendsto w atTop (𝓝 0)` for
`[0,1]`-valued `w` (ATTRIBUTION-UNVETTED as the inventory author's intent). Survivor: the `⟹`
direction.
Source: root-fa-2-003 (ii) ("is equivalent to `w_n → 0`")
Kind: P
Fidelity: exact (negation of the inventory's claim)
Hyps: (a) none -/
theorem not_forall_tendsto_imp_windowDisjoint_summable :
    ¬ ∀ w : ℕ → ℝ, (∀ n, w n ∈ Set.Icc (0 : ℝ) 1) → Tendsto w atTop (𝓝 0) →
      ∀ d : ℕ → ℕ, WindowDisjoint d → Summable (w ∘ d) :=
  fun h => not_summable_staircase_comp_tower
    (h _ staircase_mem_Icc tendsto_staircase _ windowDisjoint_tower)

/-! ## Growth -/

/-- **Growth**: a window-disjoint schedule dominates the tower, `tower k ≤ d (k+1)`.
Source: root-fa-2-003 (i) ("`d_k` … a tower in `k`")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem WindowDisjoint.tower_le {d : ℕ → ℕ} (hd : WindowDisjoint d) : ∀ k, tower k ≤ d (k + 1)
  | 0 => le_trans (Nat.one_le_two_pow) (hd.2 0)
  | k + 1 => le_trans (Nat.pow_le_pow_right two_pos (hd.tower_le k)) (hd.2 (k + 1))

/-- **Bit growth**: `d k ≤ Nat.log 2 (d (k+1))` — the `(k+1)`-st output has at least `d k`
binary digits, so no such sequence is computable in time polynomial in the *index* `k`; the
computability sentence itself stays in prose (FAF has no "e.c. in the index" object; the
intended object is the paper's Definition 4.3.7 `DeferralFunction`, polynomial in the value).
Source: root-fa-2-003 (i); [[fa-positive-results-corrected-v3]] §3 l.52
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem WindowDisjoint.le_log {d : ℕ → ℕ} (hd : WindowDisjoint d) (k : ℕ) :
    d k ≤ Nat.log 2 (d (k + 1)) :=
  Nat.le_log_of_pow_le one_lt_two (hd.2 k)

end Cleanroom.Li.TtLadder
