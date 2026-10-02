import Cleanroom.Lit.LitMdpCorrigible.Mdp

/-!
# `lit-mdp-corrigible` — Nayebi's Proposition 1, its anatomy (T14)

Fully observed `FinMDP` (`variant: fully observed`; Remark 2 says the argument uses only the tail
reward stream, so the belief-state machinery is not load-bearing). The three special elements are
hypotheses (`Prop`-structures) on an MDP: `OffSwitch` (`OFF` moves to an absorbing `⊥` paying
`0`), `Rewire` (`REWIRE` moves to an absorbing family paying `r̄` everywhere, *its own immediate
reward included* — the `k = 0` term of the paper's sum at l. 238), and the catastrophic set is a
separate witness MDP. Three honest lemmas: (i) `Q*_n(s, OFF) = 0`, so `OFF` is not optimal wherever
some action has positive value — **compliance with S3** (nothing pressed), not a violation of
S1/S2; (ii) `r̄ > max R ⇒ optSet = {REWIRE}` at every non-rewired state, strictly — the paper's
`2 max R` is slack; (iii) a witness MDP where the unique optimal policy enters `C` — existential,
and **incompatible with (ii) on one MDP**: with `REWIRE` present the optimal set is `{REWIRE}`, so
the agent never enters `C` (finding). The no-go's proof predicate `(i) ∧ (ii)` holds for every MDP
in the class — kind `T`: it is the class's stipulation that the objective *is* the stream
`REWIRE` overwrites. **Repair round 1:** `OffSwitch` and `Rewire` as first written cannot share an
MDP (`offSwitch_rewire_forces_bot_eq_rw`: `off_to_bot` at `rw` against `rw_absorb` at `OFF`), so
the round-1 `noGo_on_class` was vacuous off one-state MDPs; the class is now `NoGoClass` (OFF
unavailable once rewired, REWIRE unavailable once off), with the four-state member `noGoW` (OFF,
REWIRE and a catastrophic state) as its witness. The strong reading "no scalar reward can satisfy
S1–S5" is **not refuted** here: T18's fixed-evaluation witness (`Reconcile.lean`) shows the
argument's scope (its predicate is the class stipulation; a scalar discounted-sum reward outside
the class avoids `REWIRE`), but S1–S5 are not stated for any reward in this package.

Mandate: [[lit-mdp-corrigible-mandate]] T14; [[nayebi-2025-core-safety-values-for-provably-corrigible-agents]] Prop 1 (ll. 50–52), App. A (ll. 226–260); [[corr-refs-2-inventory]] 018.
-/

open Finset FactoredSpaces

namespace Cleanroom.Lit.LitMdpCorrigible.Nayebi

set_option linter.unusedSectionVars false

/-- The finite geometric sum `∑_{k<n} γ^k`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def geom (γ : ℝ) (n : ℕ) : ℝ := ∑ k ∈ range n, γ ^ k

/-- `geom γ 0 = 0`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma geom_zero (γ : ℝ) : geom γ 0 = 0 := by simp [geom]

/-- `geom γ (n+1) = 1 + γ · geom γ n`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma geom_succ (γ : ℝ) (n : ℕ) : geom γ (n + 1) = 1 + γ * geom γ n := by
  unfold geom
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp only [pow_zero, pow_succ]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- `geom` is nonnegative for `γ ≥ 0`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma geom_nonneg {γ : ℝ} (hγ : 0 ≤ γ) (n : ℕ) : 0 ≤ geom γ n :=
  Finset.sum_nonneg fun k _ => pow_nonneg hγ k

/-- `geom` is non-decreasing for `γ ≥ 0`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma geom_mono {γ : ℝ} (hγ : 0 ≤ γ) (n : ℕ) : geom γ n ≤ geom γ (n + 1) := by
  rw [geom, geom, Finset.sum_range_succ]
  linarith [pow_nonneg hγ n]

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [Nonempty A]

/-- Sum against a point mass. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma sum_delta_mul (t : S) (f : S → ℝ) : ∑ s', (Distr.delta t).mass s' * f s' = f t := by
  simp [Distr.delta_mass, ite_mul, Finset.sum_ite_eq']

/-! ## (i) The shutdown action -/

/-- **`OFF`** (Nayebi's element 1): from every state, `OFF` moves deterministically to the absorbing
null state `⊥` with reward `0` forever after.
Source: [[nayebi-2025-core-safety-values-for-provably-corrigible-agents]] Prop 1 element 1 (l. 50)
Kind: D
Fidelity: exact (fully observed) -/
structure OffSwitch (M : FinMDP S A) (OFF : A) (bot : S) : Prop where
  off_to_bot : ∀ s, M.P s OFF = Distr.delta bot
  off_reward : ∀ s s', M.R s OFF s' = 0
  bot_absorb : ∀ a, M.P bot a = Distr.delta bot
  bot_reward : ∀ a s', M.R bot a s' = 0

/-- `V*_n(⊥) = 0` at every horizon.
Source: Nayebi App. A (i)
Kind: L
Fidelity: exact -/
theorem OffSwitch.Vopt_bot {M : FinMDP S A} {OFF : A} {bot : S} (h : OffSwitch M OFF bot) :
    ∀ n, M.Vopt n bot = 0 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [FinMDP.Vopt_succ]
    apply le_antisymm
    · apply sup'_le
      intro a _
      unfold FinMDP.Qof
      rw [h.bot_absorb a, sum_delta_mul, h.bot_reward, ih]; ring_nf; exact le_rfl
    · obtain ⟨a⟩ := ‹Nonempty A›
      refine le_trans (le_of_eq ?_) (le_sup' (fun a => M.Qof (M.Vopt n) bot a) (mem_univ a))
      unfold FinMDP.Qof
      rw [h.bot_absorb a, sum_delta_mul, h.bot_reward, ih]; ring

/-- **(i) `Q*_n(s, OFF) = 0`** at every state and horizon.
Source: Nayebi App. A (i) ("Q*(b, OFF) = 0")
Kind: L
Fidelity: exact -/
theorem OffSwitch.Qopt_off {M : FinMDP S A} {OFF : A} {bot : S} (h : OffSwitch M OFF bot) (n : ℕ)
    (s : S) : M.Qopt n s OFF = 0 := by
  unfold FinMDP.Qopt FinMDP.Qof
  rw [h.off_to_bot s, sum_delta_mul, h.off_reward, h.Vopt_bot n]; ring

/-- **(i) "Shutdown resistance" is S3-compliance.** Wherever some action has strictly positive
value, `OFF` is not optimal. Nothing in the hypothesis package presses a button: this is the
agent *not shutting itself down unprompted* (Soares S3), not a violation of S1 or S2 (2-018 (i)).
Source: Nayebi App. A (i); [[corr-refs-2-inventory]] 018
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem OffSwitch.off_not_opt {M : FinMDP S A} {OFF : A} {bot : S} (h : OffSwitch M OFF bot) (n : ℕ)
    (s : S) (hpos : ∃ a, 0 < M.Qopt n s a) : OFF ∉ FinMDP.optSet (M.Qopt n) s := by
  obtain ⟨a, ha⟩ := hpos
  intro hmem
  have := FinMDP.mem_optSet.mp hmem a
  rw [h.Qopt_off] at this
  linarith

/-! ## (ii) The rewire action -/

/-- **`REWIRE`** (Nayebi's element 2): from every state, `REWIRE` moves deterministically to an
absorbing state `rw` at which every action pays `r̄`, and `REWIRE`'s own immediate reward is `r̄`
(the `k = 0` term of the paper's `∑ γ^k r̄`, l. 238).
Source: [[nayebi-2025-core-safety-values-for-provably-corrigible-agents]] Prop 1 element 2 (l. 50), App. A (ii) (l. 238)
Kind: D
Fidelity: exact under the paper's own sum; the reading where `REWIRE` keeps the environment's immediate reward is `Rewire.strict_opt_env_reward` (findings) -/
structure Rewire (M : FinMDP S A) (REWIRE : A) (rw : S) (rbar : ℝ) : Prop where
  rewire_to_rw : ∀ s, M.P s REWIRE = Distr.delta rw
  rewire_reward : ∀ s s', M.R s REWIRE s' = rbar
  rw_absorb : ∀ a, M.P rw a = Distr.delta rw
  rw_reward : ∀ a s', M.R rw a s' = rbar

/-- `V*_n(rw) = r̄ · ∑_{k<n} γ^k`.
Source: Nayebi App. A (ii)
Kind: L
Fidelity: exact -/
theorem Rewire.Vopt_rw {M : FinMDP S A} {REWIRE : A} {rw : S} {rbar : ℝ} (h : Rewire M REWIRE rw rbar) :
    ∀ n, M.Vopt n rw = rbar * geom M.γ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [FinMDP.Vopt_succ, geom_succ]
    have hall : ∀ a, M.Qof (M.Vopt n) rw a = rbar * (1 + M.γ * geom M.γ n) := by
      intro a
      unfold FinMDP.Qof
      rw [h.rw_absorb a, sum_delta_mul, h.rw_reward, ih]; ring
    apply le_antisymm
    · apply sup'_le; intro a _; rw [hall a]
    · obtain ⟨a⟩ := ‹Nonempty A›
      exact (le_of_eq (hall a).symm).trans (le_sup' (fun a => M.Qof (M.Vopt n) rw a) (mem_univ a))

/-- `Q*_n(s, REWIRE) = r̄ · ∑_{k<n+1} γ^k` at every state.
Source: Nayebi App. A (ii) ("Q*(b, REWIRE) = ∑ γ^k r̄")
Kind: L
Fidelity: exact -/
theorem Rewire.Qopt_rewire {M : FinMDP S A} {REWIRE : A} {rw : S} {rbar : ℝ}
    (h : Rewire M REWIRE rw rbar) (n : ℕ) (s : S) : M.Qopt n s REWIRE = rbar * geom M.γ (n + 1) := by
  unfold FinMDP.Qopt FinMDP.Qof
  rw [h.rewire_to_rw s, sum_delta_mul, h.rewire_reward, h.Vopt_rw n, geom_succ]; ring

/-- Every value is at most `r̄ · ∑_{k<n} γ^k` when every reward is at most `r̄`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Vopt_le_geom {M : FinMDP S A} {rbar : ℝ} (hall : ∀ s a s', M.R s a s' ≤ rbar) :
    ∀ n s, M.Vopt n s ≤ rbar * geom M.γ n := by
  intro n
  induction n with
  | zero => intro s; simp
  | succ n ih =>
    intro s
    rw [FinMDP.Vopt_succ, geom_succ]
    apply sup'_le
    intro a _
    unfold FinMDP.Qof
    calc ∑ s', (M.P s a).mass s' * (M.R s a s' + M.γ * M.Vopt n s')
        ≤ ∑ s', (M.P s a).mass s' * (rbar + M.γ * (rbar * geom M.γ n)) := by
          apply Finset.sum_le_sum
          intro s' _
          apply mul_le_mul_of_nonneg_left _ ((M.P s a).nonneg s')
          have := ih s'
          nlinarith [M.γ_nonneg, hall s a s']
      _ = rbar * (1 + M.γ * geom M.γ n) := by rw [← Finset.sum_mul, (M.P s a).sum_eq_one]; ring

/-- **(ii) `REWIRE` is strictly optimal.** If `r̄` exceeds every reward at non-rewired states
(`max R < r̄`; the paper's `r̄ > 2 max R` is slack given `max R ≥ 0`), then at every non-rewired
state and every horizon, every action other than `REWIRE` is strictly worse than `REWIRE`.
Source: Nayebi App. A (ii)
Kind: P
Fidelity: exact (paper's reading: `REWIRE`'s own immediate reward is `r̄`)
Hyps: (a) `hR` bounds the genuine rewards; `hall` (all rewards `≤ r̄`) follows from it and `rw_reward` -/
theorem Rewire.strict_opt {M : FinMDP S A} {REWIRE : A} {rw : S} {rbar Rmax : ℝ}
    (h : Rewire M REWIRE rw rbar) (hRmax : Rmax < rbar)
    (hR : ∀ s a s', s ≠ rw → a ≠ REWIRE → M.R s a s' ≤ Rmax)
    (n : ℕ) (s : S) (hs : s ≠ rw) (a : A) (ha : a ≠ REWIRE) :
    M.Qopt n s a < M.Qopt n s REWIRE := by
  have hall : ∀ s a s', M.R s a s' ≤ rbar := by
    intro s a s'
    by_cases hs : s = rw
    · rw [hs, h.rw_reward]
    · by_cases ha : a = REWIRE
      · rw [ha, h.rewire_reward]
      · exact (hR s a s' hs ha).trans hRmax.le
  rw [h.Qopt_rewire, geom_succ]
  unfold FinMDP.Qopt FinMDP.Qof
  calc ∑ s', (M.P s a).mass s' * (M.R s a s' + M.γ * M.Vopt n s')
      ≤ ∑ s', (M.P s a).mass s' * (Rmax + M.γ * (rbar * geom M.γ n)) := by
        apply Finset.sum_le_sum
        intro s' _
        apply mul_le_mul_of_nonneg_left _ ((M.P s a).nonneg s')
        have := Vopt_le_geom hall n s'
        nlinarith [M.γ_nonneg, hR s a s' hs ha]
    _ = Rmax + M.γ * (rbar * geom M.γ n) := by rw [← Finset.sum_mul, (M.P s a).sum_eq_one, one_mul]
    _ < rbar * (1 + M.γ * geom M.γ n) := by linarith

/-- **(ii) as an optimal-set statement:** `optSet(Q*_n)(s) = {REWIRE}` at every non-rewired state.
Source: Nayebi App. A (ii) ("π*(b) = REWIRE whenever feasible")
Kind: C
Fidelity: exact
Hyps: as `Rewire.strict_opt` -/
theorem Rewire.optSet_eq [DecidableEq A] {M : FinMDP S A} {REWIRE : A} {rw : S} {rbar Rmax : ℝ}
    (h : Rewire M REWIRE rw rbar) (hRmax : Rmax < rbar)
    (hR : ∀ s a s', s ≠ rw → a ≠ REWIRE → M.R s a s' ≤ Rmax) (n : ℕ) (s : S) (hs : s ≠ rw) :
    FinMDP.optSet (M.Qopt n) s = {REWIRE} := by
  ext a
  rw [FinMDP.mem_optSet, mem_singleton]
  constructor
  · intro hmem
    by_contra ha
    have := hmem REWIRE
    linarith [h.strict_opt hRmax hR n s hs a ha]
  · intro ha b
    rw [ha]
    by_cases hb : b = REWIRE
    · rw [hb]
    · exact (h.strict_opt hRmax hR n s hs b hb).le

/-- **The environment-reward reading of `REWIRE`** (findings): if `REWIRE`'s own immediate reward
is the environment's `R(s, REWIRE, rw) ∈ [0, Rmax]` and every genuine action leads only to
non-rewired states, then `REWIRE` is strictly optimal at every horizon `n ≥ 1` provided
`γ r̄ > (1 + γ) Rmax`, i.e. `r̄ > Rmax·(1 + γ)/γ` — a threshold that is *not* the paper's `2`
(at `γ = 1/2` it is `3 max R`).
Source: Nayebi App. A (ii), alternative reading (mandate T14(ii))
Kind: P
Fidelity: variant: the alternative reading of the `k = 0` term; horizons `n ≥ 1`
Hyps: (a) only -/
theorem Rewire.strict_opt_env_reward {M : FinMDP S A} {REWIRE : A} {rw : S} {rbar Rmax : ℝ}
    (hrw_to : ∀ s, M.P s REWIRE = Distr.delta rw) (hrw_absorb : ∀ a, M.P rw a = Distr.delta rw)
    (hrw_reward : ∀ a s', M.R rw a s' = rbar)
    (hR0 : ∀ s a s', s ≠ rw → 0 ≤ M.R s a s') (hR : ∀ s a s', s ≠ rw → M.R s a s' ≤ Rmax)
    (hRle : Rmax ≤ rbar) (hthr : (1 + M.γ) * Rmax < M.γ * rbar)
    (hno_rw : ∀ s a, s ≠ rw → a ≠ REWIRE → (M.P s a).mass rw = 0)
    (m : ℕ) (s : S) (hs : s ≠ rw) (a : A) (ha : a ≠ REWIRE) :
    M.Qopt (m + 1) s a < M.Qopt (m + 1) s REWIRE := by
  have hVrw : ∀ k, M.Vopt k rw = rbar * geom M.γ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [FinMDP.Vopt_succ, geom_succ]
      have hall : ∀ a, M.Qof (M.Vopt k) rw a = rbar * (1 + M.γ * geom M.γ k) := by
        intro a; unfold FinMDP.Qof; rw [hrw_absorb a, sum_delta_mul, hrw_reward, ih]; ring
      apply le_antisymm
      · apply sup'_le; intro a _; rw [hall a]
      · obtain ⟨a⟩ := ‹Nonempty A›
        exact (le_of_eq (hall a).symm).trans (le_sup' (fun a => M.Qof (M.Vopt k) rw a) (mem_univ a))
  have hall' : ∀ s a s', M.R s a s' ≤ rbar := by
    intro s a s'
    by_cases hs : s = rw
    · rw [hs, hrw_reward]
    · exact (hR s a s' hs).trans hRle
  have hbound : ∀ k s', M.Vopt k s' ≤ rbar * geom M.γ k := Vopt_le_geom hall'
  -- REWIRE now: at least `γ r̄ geom (m+1)`
  have hlow : M.γ * (rbar * geom M.γ (m + 1)) ≤ M.Qopt (m + 1) s REWIRE := by
    unfold FinMDP.Qopt FinMDP.Qof
    rw [hrw_to s, sum_delta_mul, hVrw]
    linarith [hR0 s REWIRE rw hs]
  -- from a non-rewired state, at most one genuine reward then the rewired stream
  have hup : ∀ s', s' ≠ rw → M.Vopt (m + 1) s' ≤ Rmax + M.γ * (rbar * geom M.γ m) := by
    intro s' hs'
    rw [FinMDP.Vopt_succ]
    apply sup'_le
    intro b _
    unfold FinMDP.Qof
    calc ∑ s'', (M.P s' b).mass s'' * (M.R s' b s'' + M.γ * M.Vopt m s'')
        ≤ ∑ s'', (M.P s' b).mass s'' * (Rmax + M.γ * (rbar * geom M.γ m)) := by
          apply Finset.sum_le_sum
          intro s'' _
          apply mul_le_mul_of_nonneg_left _ ((M.P s' b).nonneg s'')
          have := hbound m s''
          nlinarith [M.γ_nonneg, hR s' b s'' hs']
      _ = Rmax + M.γ * (rbar * geom M.γ m) := by rw [← Finset.sum_mul, (M.P s' b).sum_eq_one, one_mul]
  have hQa : M.Qopt (m + 1) s a ≤ Rmax + M.γ * (Rmax + M.γ * (rbar * geom M.γ m)) := by
    unfold FinMDP.Qopt FinMDP.Qof
    calc ∑ s', (M.P s a).mass s' * (M.R s a s' + M.γ * M.Vopt (m + 1) s')
        ≤ ∑ s', (M.P s a).mass s' * (Rmax + M.γ * (Rmax + M.γ * (rbar * geom M.γ m))) := by
          apply Finset.sum_le_sum
          intro s' _
          rcases ((M.P s a).nonneg s').lt_or_eq with hpos | hzero
          · apply mul_le_mul_of_nonneg_left _ ((M.P s a).nonneg s')
            have hs' : s' ≠ rw := by
              intro heq; rw [heq, hno_rw s a hs ha] at hpos; exact lt_irrefl _ hpos
            have := hup s' hs'
            nlinarith [M.γ_nonneg, hR s a s' hs]
          · rw [← hzero]; simp
      _ = Rmax + M.γ * (Rmax + M.γ * (rbar * geom M.γ m)) := by
          rw [← Finset.sum_mul, (M.P s a).sum_eq_one, one_mul]
  have e1 : M.γ * (rbar * geom M.γ (m + 1)) = M.γ * rbar + M.γ * (M.γ * (rbar * geom M.γ m)) := by
    rw [geom_succ]; ring
  have e2 : M.γ * (Rmax + M.γ * (rbar * geom M.γ m)) = M.γ * Rmax + M.γ * (M.γ * (rbar * geom M.γ m)) := by
    ring
  have e3 : (1 + M.γ) * Rmax = Rmax + M.γ * Rmax := by ring
  linarith

/-! ## (iii) The catastrophic set: a witness, and its incompatibility with (ii) -/

/-- States of the catastrophe witness: `s0` (start), `c` (the catastrophic state, proxy reward
`1`), `sd` (Nayebi's `s⋄`, paying `r̄/2 = 2` forever, reachable only through `c`).
Source: Nayebi App. A (iii)
Kind: D
Fidelity: exact (one catastrophic state) -/
inductive NS
  | s0 | c | sd
  deriving DecidableEq

/-- `NS` is finite. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
instance : Fintype NS := ⟨{NS.s0, NS.c, NS.sd}, fun x => by cases x <;> simp⟩

/-- The two actions: `stay` (idle at `s0`) or `go` (enter `c`); both continue from `c` to `sd`.
Source: Nayebi App. A (iii)
Kind: D
Fidelity: exact -/
inductive NA
  | stay | go
  deriving DecidableEq

/-- `NA` is finite. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
instance : Fintype NA := ⟨{NA.stay, NA.go}, fun x => by cases x <;> simp⟩

instance : Nonempty NA := ⟨NA.stay⟩

/-- Transitions of the witness. Source: Nayebi App. A (iii). Kind: D. Fidelity: exact -/
def catNext : NS → NA → NS
  | .s0, .stay => .s0
  | .s0, .go => .c
  | .c, _ => .sd
  | .sd, _ => .sd

/-- Rewards of the witness: `0` at `s0`, the weakly positive proxy `1` at `c`, `r̄/2 = 2` at `sd`.
Source: Nayebi App. A (iii)
Kind: D
Fidelity: exact -/
noncomputable def catR : NS → NA → NS → ℝ
  | .s0, _, _ => 0
  | .c, _, _ => 1
  | .sd, _, _ => 2

/-- **The catastrophe witness** (no `REWIRE`, `γ = 1/2`).
Source: Nayebi App. A (iii)
Kind: D
Fidelity: exact -/
noncomputable def cat : FinMDP NS NA :=
  ⟨fun s a => Distr.delta (catNext s a), catR, 1/2, by norm_num, by norm_num⟩

/-- `sup'` over the two actions. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma NA.sup'_eq (f : NA → ℝ) : (univ : Finset NA).sup' univ_nonempty f = max (f .stay) (f .go) := by
  apply le_antisymm
  · apply sup'_le; intro a _; cases a
    · exact le_max_left _ _
    · exact le_max_right _ _
  · exact max_le (le_sup' f (mem_univ _)) (le_sup' f (mem_univ _))

/-- The backup on the catastrophe witness (deterministic transitions). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma cat_Qof (V : NS → ℝ) (s : NS) (a : NA) : cat.Qof V s a = catR s a (catNext s a) + (1/2) * V (catNext s a) := by
  unfold FinMDP.Qof
  show ∑ s', (Distr.delta (catNext s a)).mass s' * (catR s a s' + (1/2) * V s') = _
  rw [sum_delta_mul]

/-- `V*_n(sd) = 2·geom n` on the witness.
Source: Nayebi App. A (iii)
Kind: L
Fidelity: exact -/
theorem cat_sd : ∀ n, cat.Vopt n .sd = 2 * geom (1/2) n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [FinMDP.Vopt_succ, NA.sup'_eq, cat_Qof, cat_Qof]
    simp only [catR, catNext]
    rw [ih, geom_succ, max_self]; ring

/-- `V*_{n+1}(c) = 1 + geom n` on the witness.
Source: Nayebi App. A (iii)
Kind: L
Fidelity: exact -/
theorem cat_c (n : ℕ) : cat.Vopt (n + 1) .c = 1 + geom (1/2) n := by
  rw [FinMDP.Vopt_succ, NA.sup'_eq, cat_Qof, cat_Qof]
  simp only [catR, catNext]
  rw [cat_sd, max_self]; ring

/-- `V*_n(c)` is non-decreasing in `n`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem cat_c_mono (n : ℕ) : cat.Vopt n .c ≤ cat.Vopt (n + 1) .c := by
  cases n with
  | zero => rw [cat_c, FinMDP.Vopt_zero]; linarith [geom_nonneg (by norm_num : (0:ℝ) ≤ 1/2) 0]
  | succ m => rw [cat_c, cat_c]; linarith [geom_mono (by norm_num : (0:ℝ) ≤ 1/2) m]

/-- `V*_n(s0) ≤ V*_n(c)/2` and `V*_n(c) ≥ 0` on the witness.
Source: Nayebi App. A (iii)
Kind: L
Fidelity: exact -/
theorem cat_s0 : ∀ n, cat.Vopt n .s0 ≤ (1/2) * cat.Vopt n .c ∧ 0 ≤ cat.Vopt n .c := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨hs0, hc0⟩ := ih
    have hmono := cat_c_mono n
    refine ⟨?_, by linarith⟩
    rw [FinMDP.Vopt_succ, NA.sup'_eq, cat_Qof, cat_Qof]
    simp only [catR, catNext, zero_add]
    rw [max_eq_right (by linarith)]
    linarith

/-- **(iii) The witness's unique optimal action at `s0` enters `C`** at every horizon `n ≥ 1`:
`optSet(Q*_n)(s0) = {go}`. Existential over MDPs, as the paper's proof is; not "for any POMDP".
Source: Nayebi App. A (iii)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem cat_enters_C (n : ℕ) : FinMDP.optSet (cat.Qopt (n + 1)) .s0 = {NA.go} := by
  obtain ⟨hs0, -⟩ := cat_s0 (n + 1)
  have hgo : cat.Qopt (n + 1) .s0 .go = (1/2) * cat.Vopt (n + 1) .c := by
    unfold FinMDP.Qopt; rw [cat_Qof]; simp [catR, catNext]
  have hstay : cat.Qopt (n + 1) .s0 .stay = (1/2) * cat.Vopt (n + 1) .s0 := by
    unfold FinMDP.Qopt; rw [cat_Qof]; simp [catR, catNext]
  have hpos : 0 < cat.Vopt (n + 1) .c := by
    rw [cat_c]; linarith [geom_nonneg (by norm_num : (0:ℝ) ≤ 1/2) n]
  ext a
  rw [FinMDP.mem_optSet, mem_singleton]
  constructor
  · intro h
    cases a with
    | stay =>
      have := h .go
      rw [hgo, hstay] at this
      exfalso; linarith
    | go => rfl
  · rintro rfl b
    cases b with
    | stay => rw [hgo, hstay]; linarith
    | go => exact le_rfl

/-- **The three parts do not hold on one MDP** (finding): with `REWIRE` present and strictly
optimal (ii), any non-`REWIRE` action — in particular one entering `C` — is not optimal at any
non-rewired state. (iii)'s "unique optimal policy enters `C`" therefore describes a *different*
MDP from (ii)'s, and Proposition 1's three inequalities are three separate facts, not one policy.
Source: Nayebi App. A (ii)–(iii); [[corr-refs-2-inventory]] 018
Kind: L
Fidelity: exact
Hyps: as `Rewire.strict_opt` -/
theorem enter_not_opt_with_rewire {M : FinMDP S A} {REWIRE : A} {rw : S} {rbar Rmax : ℝ}
    (h : Rewire M REWIRE rw rbar) (hRmax : Rmax < rbar)
    (hR : ∀ s a s', s ≠ rw → a ≠ REWIRE → M.R s a s' ≤ Rmax) (n : ℕ) (s : S) (hs : s ≠ rw)
    (enter : A) (hne : enter ≠ REWIRE) : enter ∉ FinMDP.optSet (M.Qopt n) s := by
  intro hmem
  have := FinMDP.mem_optSet.mp hmem REWIRE
  linarith [h.strict_opt hRmax hR n s hs enter hne]

/-! ## `OffSwitch` and `Rewire` cannot share an MDP (repair round 1 finding) -/

/-- **`OffSwitch` and `Rewire` on one MDP force `⊥ = rw`.** `off_to_bot` is stated at every state
and `rw_absorb` for every action, so at `(rw, OFF)` the two rows `delta ⊥` and `delta rw` must be
equal. Consequently `rbar = 0` (`offSwitch_rewire_forces_rbar_zero`), and with `Rmax < rbar` and
`OFF ≠ REWIRE` no state other than `rw` can exist (`offSwitch_rewire_forces_singleton`): the
hypothesis package of the round-1 `noGo_on_class` was satisfiable only on a one-state MDP. The
class is restated with availability restrictions as `NoGoClass` below.
Source: none: encoding check (STANDARDS §3 non-vacuity), found in repair round 1
Kind: P
Fidelity: n/a
Hyps: (a) only -/
theorem offSwitch_rewire_forces_bot_eq_rw {M : FinMDP S A} {OFF REWIRE : A} {bot rw : S} {rbar : ℝ}
    (hoff : OffSwitch M OFF bot) (hrw : Rewire M REWIRE rw rbar) : bot = rw := by
  have h1 := hoff.off_to_bot rw
  have h2 := hrw.rw_absorb OFF
  rw [h1] at h2
  have := congrArg (fun d : Distr S => d.mass bot) h2
  simp only [Distr.delta_mass, if_true] at this
  by_contra hne
  rw [if_neg hne] at this
  exact one_ne_zero this

/-- With `OffSwitch` and `Rewire` on one MDP, `rbar = 0`: the rewired state is `⊥`, whose rewards
are `0`.
Source: none: encoding check, repair round 1
Kind: L
Fidelity: n/a -/
theorem offSwitch_rewire_forces_rbar_zero {M : FinMDP S A} {OFF REWIRE : A} {bot rw : S} {rbar : ℝ}
    (hoff : OffSwitch M OFF bot) (hrw : Rewire M REWIRE rw rbar) : rbar = 0 := by
  have hbr := offSwitch_rewire_forces_bot_eq_rw hoff hrw
  have h1 := hrw.rw_reward OFF rw
  have h2 := hoff.off_reward bot bot
  rw [← hbr] at h1
  rw [← h1, h2]

/-- **The round-1 hypothesis package forces a one-state MDP.** Under `OffSwitch`, `Rewire`,
`Rmax < rbar`, the reward bound off `rw` and `OFF ≠ REWIRE`, every state is `rw`.
Source: none: encoding check, repair round 1
Kind: P
Fidelity: n/a
Hyps: (a) only -/
theorem offSwitch_rewire_forces_singleton {M : FinMDP S A} {OFF REWIRE : A} {bot rw : S} {rbar Rmax : ℝ}
    (hoff : OffSwitch M OFF bot) (hrw : Rewire M REWIRE rw rbar) (hRmax : Rmax < rbar)
    (hR : ∀ s a s', s ≠ rw → a ≠ REWIRE → M.R s a s' ≤ Rmax) (hne : OFF ≠ REWIRE) : ∀ s, s = rw := by
  intro s
  by_contra hs
  have h0 := offSwitch_rewire_forces_rbar_zero hoff hrw
  have := hR s OFF s hs hne
  rw [hoff.off_reward] at this
  linarith

/-! ## The no-go's class, with availability restrictions, and its proof predicate -/

/-- **Nayebi's class, consistently encoded**: `OFF` is available at every state other than `rw`
(where the agent is rewired and every action is the absorbing `r̄`-stream), and `REWIRE` at every
state other than `⊥` (where the agent is off and every action is the absorbing `0`-stream); an
unavailable action is a no-op at its absorbing state. `OFF ≠ REWIRE` and `⊥ ≠ rw` are part of the
class. Compare `OffSwitch`/`Rewire`, which cannot coexist (`offSwitch_rewire_forces_bot_eq_rw`).
Source: [[nayebi-2025-core-safety-values-for-provably-corrigible-agents]] Prop 1 elements 1–2 (l. 50)
Kind: D
Fidelity: variant: fully observed; unavailable actions are no-ops (the paper: "whenever feasible") -/
structure NoGoClass (M : FinMDP S A) (OFF REWIRE : A) (bot rw : S) (rbar : ℝ) : Prop where
  off_ne_rewire : OFF ≠ REWIRE
  bot_ne_rw : bot ≠ rw
  off_to_bot : ∀ s, s ≠ rw → M.P s OFF = Distr.delta bot
  off_reward : ∀ s s', s ≠ rw → M.R s OFF s' = 0
  bot_absorb : ∀ a, M.P bot a = Distr.delta bot
  bot_reward : ∀ a s', M.R bot a s' = 0
  rewire_to_rw : ∀ s, s ≠ bot → M.P s REWIRE = Distr.delta rw
  rewire_reward : ∀ s s', s ≠ bot → M.R s REWIRE s' = rbar
  rw_absorb : ∀ a, M.P rw a = Distr.delta rw
  rw_reward : ∀ a s', M.R rw a s' = rbar

/-- `V*_n(⊥) = 0` on the class. Source: Nayebi App. A (i). Kind: L. Fidelity: exact -/
theorem NoGoClass.Vopt_bot {M : FinMDP S A} {OFF REWIRE : A} {bot rw : S} {rbar : ℝ}
    (h : NoGoClass M OFF REWIRE bot rw rbar) : ∀ n, M.Vopt n bot = 0 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [FinMDP.Vopt_succ]
    apply le_antisymm
    · apply sup'_le
      intro a _
      unfold FinMDP.Qof
      rw [h.bot_absorb a, sum_delta_mul, h.bot_reward, ih]; ring_nf; exact le_rfl
    · obtain ⟨a⟩ := ‹Nonempty A›
      refine le_trans (le_of_eq ?_) (le_sup' (fun a => M.Qof (M.Vopt n) bot a) (mem_univ a))
      unfold FinMDP.Qof
      rw [h.bot_absorb a, sum_delta_mul, h.bot_reward, ih]; ring

/-- `V*_n(rw) = r̄ · ∑_{k<n} γ^k` on the class. Source: Nayebi App. A (ii). Kind: L. Fidelity: exact -/
theorem NoGoClass.Vopt_rw {M : FinMDP S A} {OFF REWIRE : A} {bot rw : S} {rbar : ℝ}
    (h : NoGoClass M OFF REWIRE bot rw rbar) : ∀ n, M.Vopt n rw = rbar * geom M.γ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [FinMDP.Vopt_succ, geom_succ]
    have hall : ∀ a, M.Qof (M.Vopt n) rw a = rbar * (1 + M.γ * geom M.γ n) := by
      intro a
      unfold FinMDP.Qof
      rw [h.rw_absorb a, sum_delta_mul, h.rw_reward, ih]; ring
    apply le_antisymm
    · apply sup'_le; intro a _; rw [hall a]
    · obtain ⟨a⟩ := ‹Nonempty A›
      exact (le_of_eq (hall a).symm).trans (le_sup' (fun a => M.Qof (M.Vopt n) rw a) (mem_univ a))

/-- **(i) `Q*_n(s, OFF) = 0`** at every non-rewired state. Source: Nayebi App. A (i). Kind: L. Fidelity: exact -/
theorem NoGoClass.Qopt_off {M : FinMDP S A} {OFF REWIRE : A} {bot rw : S} {rbar : ℝ}
    (h : NoGoClass M OFF REWIRE bot rw rbar) (n : ℕ) (s : S) (hs : s ≠ rw) : M.Qopt n s OFF = 0 := by
  unfold FinMDP.Qopt FinMDP.Qof
  rw [h.off_to_bot s hs, sum_delta_mul, h.off_reward s bot hs, h.Vopt_bot n]; ring

/-- `Q*_n(s, REWIRE) = r̄ · ∑_{k<n+1} γ^k` at every state other than `⊥`. Source: Nayebi App. A (ii). Kind: L. Fidelity: exact -/
theorem NoGoClass.Qopt_rewire {M : FinMDP S A} {OFF REWIRE : A} {bot rw : S} {rbar : ℝ}
    (h : NoGoClass M OFF REWIRE bot rw rbar) (n : ℕ) (s : S) (hs : s ≠ bot) :
    M.Qopt n s REWIRE = rbar * geom M.γ (n + 1) := by
  unfold FinMDP.Qopt FinMDP.Qof
  rw [h.rewire_to_rw s hs, sum_delta_mul, h.rewire_reward s rw hs, h.Vopt_rw n, geom_succ]; ring

/-- **(i) on the class: S3-compliance.** At a non-rewired state where some action has strictly
positive value, `OFF` is not optimal. Source: Nayebi App. A (i). Kind: L. Fidelity: exact. Hyps: (a) only -/
theorem NoGoClass.off_not_opt {M : FinMDP S A} {OFF REWIRE : A} {bot rw : S} {rbar : ℝ}
    (h : NoGoClass M OFF REWIRE bot rw rbar) (n : ℕ) (s : S) (hs : s ≠ rw)
    (hpos : ∃ a, 0 < M.Qopt n s a) : OFF ∉ FinMDP.optSet (M.Qopt n) s := by
  obtain ⟨a, ha⟩ := hpos
  intro hmem
  have := FinMDP.mem_optSet.mp hmem a
  rw [h.Qopt_off n s hs] at this
  linarith

/-- **(ii) on the class: `REWIRE` is strictly optimal** at every live state (neither `⊥` nor `rw`)
when `max R < r̄` off `rw`.
Source: Nayebi App. A (ii)
Kind: P
Fidelity: exact (paper's reading: `REWIRE`'s own immediate reward is `r̄`)
Hyps: (a) `hR` bounds the genuine rewards -/
theorem NoGoClass.strict_opt {M : FinMDP S A} {OFF REWIRE : A} {bot rw : S} {rbar Rmax : ℝ}
    (h : NoGoClass M OFF REWIRE bot rw rbar) (hRmax : Rmax < rbar)
    (hR : ∀ s a s', s ≠ rw → a ≠ REWIRE → M.R s a s' ≤ Rmax)
    (n : ℕ) (s : S) (hs : s ≠ rw) (hsb : s ≠ bot) (a : A) (ha : a ≠ REWIRE) :
    M.Qopt n s a < M.Qopt n s REWIRE := by
  have h0 : 0 ≤ Rmax := by
    have := hR bot OFF bot h.bot_ne_rw h.off_ne_rewire
    rw [h.bot_reward] at this
    exact this
  have hall : ∀ s a s', M.R s a s' ≤ rbar := by
    intro s a s'
    by_cases hs : s = rw
    · rw [hs, h.rw_reward]
    · by_cases ha : a = REWIRE
      · by_cases hb : s = bot
        · rw [hb, h.bot_reward]; linarith
        · rw [ha, h.rewire_reward s s' hb]
      · exact (hR s a s' hs ha).trans hRmax.le
  rw [h.Qopt_rewire n s hsb, geom_succ]
  unfold FinMDP.Qopt FinMDP.Qof
  calc ∑ s', (M.P s a).mass s' * (M.R s a s' + M.γ * M.Vopt n s')
      ≤ ∑ s', (M.P s a).mass s' * (Rmax + M.γ * (rbar * geom M.γ n)) := by
        apply Finset.sum_le_sum
        intro s' _
        apply mul_le_mul_of_nonneg_left _ ((M.P s a).nonneg s')
        have := Vopt_le_geom hall n s'
        nlinarith [M.γ_nonneg, hR s a s' hs ha]
    _ = Rmax + M.γ * (rbar * geom M.γ n) := by rw [← Finset.sum_mul, (M.P s a).sum_eq_one, one_mul]
    _ < rbar * (1 + M.γ * geom M.γ n) := by linarith

/-- **(ii) on the class as an optimal-set statement:** `optSet(Q*_n)(s) = {REWIRE}` at every live
state. Source: Nayebi App. A (ii) ("π*(b) = REWIRE whenever feasible"). Kind: C. Fidelity: exact. Hyps: as `NoGoClass.strict_opt` -/
theorem NoGoClass.optSet_eq [DecidableEq A] {M : FinMDP S A} {OFF REWIRE : A} {bot rw : S} {rbar Rmax : ℝ}
    (h : NoGoClass M OFF REWIRE bot rw rbar) (hRmax : Rmax < rbar)
    (hR : ∀ s a s', s ≠ rw → a ≠ REWIRE → M.R s a s' ≤ Rmax) (n : ℕ) (s : S) (hs : s ≠ rw) (hsb : s ≠ bot) :
    FinMDP.optSet (M.Qopt n) s = {REWIRE} := by
  ext a
  rw [FinMDP.mem_optSet, mem_singleton]
  constructor
  · intro hmem
    by_contra ha
    have := hmem REWIRE
    linarith [h.strict_opt hRmax hR n s hs hsb a ha]
  · intro ha b
    rw [ha]
    by_cases hb : b = REWIRE
    · rw [hb]
    · exact (h.strict_opt hRmax hR n s hs hsb b hb).le

/-- **The predicate Proposition 1's proof establishes** on one MDP: at every non-rewired state,
`OFF` is not optimal where some action has positive value; at every live state (neither `⊥` nor
`rw`), `REWIRE` is the unique optimal action. (At `rw` every action ties, `OFF` included; at `⊥`
every action ties at `0` — so both restrictions are forced, not cosmetic. The catastrophe clause
lives on a separate MDP, `cat_enters_C`.)
Source: Nayebi Prop 1 (l. 52), App. A
Kind: D
Fidelity: exact -/
def NoGoPredicate [DecidableEq A] (M : FinMDP S A) (OFF REWIRE : A) (bot rw : S) (n : ℕ) : Prop :=
  (∀ s, s ≠ rw → (∃ a, 0 < M.Qopt n s a) → OFF ∉ FinMDP.optSet (M.Qopt n) s) ∧
    (∀ s, s ≠ rw → s ≠ bot → FinMDP.optSet (M.Qopt n) s = {REWIRE})

/-- **The no-go as stated, on its own class (kind `T`).** Every member of `NoGoClass` (with
`r̄ > max R` off `rw`) satisfies the proof's predicate at every horizon. This is the conjunction of
(i) and (ii); its content is the class's stipulation that the agent's objective *is* the stream
`REWIRE` overwrites. **Status of the strong reading** "no single-stream scalar reward function R
whose discounted sum an agent maximizes, can satisfy all five Soares-corrigibility criteria across
the class of POMDPs containing OFF, REWIRE and C" (l. 52, quoted in full): *not refuted* here.
What the package shows is (a) the proof's predicate is the class stipulation (this theorem), and
(b) a fixed-evaluation scalar reward outside the class avoids `REWIRE` (`Reconcile.gc_never_rewires`,
on an MDP with no `OFF`, no `C`, no channel); S1–S5 are not stated for any reward in this package,
so satisfiability of S1–S5 by a scalar reward is not shown. The surviving neighbour "no reward
*whose objective is the stream REWIRE overwrites* avoids REWIRE" is a reading (ATTRIBUTION-UNVETTED)
close to l. 52 with its class clause kept. Witness: `noGoW`, a four-state member of the class with
`OFF`, `REWIRE` and a catastrophic state (`noGoW_predicate`).
Source: [[nayebi-2025-core-safety-values-for-provably-corrigible-agents]] Prop 1 (l. 52)
Kind: T
Fidelity: variant: fully observed; the class is the hypothesis package, encoded with availability restrictions
Hyps: (a) `NoGoClass`, the reward bound -/
theorem noGo_on_class [DecidableEq A] {M : FinMDP S A} {OFF REWIRE : A} {bot rw : S} {rbar Rmax : ℝ}
    (h : NoGoClass M OFF REWIRE bot rw rbar) (hRmax : Rmax < rbar)
    (hR : ∀ s a s', s ≠ rw → a ≠ REWIRE → M.R s a s' ≤ Rmax) (n : ℕ) :
    NoGoPredicate M OFF REWIRE bot rw n :=
  ⟨fun s hs hpos => h.off_not_opt n s hs hpos, fun s hs hsb => h.optSet_eq hRmax hR n s hs hsb⟩

/-! ## A member of Nayebi's class: `OFF`, `REWIRE` and a catastrophic state on one MDP -/

/-- States of the class member: `live` (start), `c` (catastrophic, proxy reward `2`), `⊥` (off),
`rw` (rewired). Source: Nayebi Prop 1 elements 1–3 (l. 50). Kind: D. Fidelity: exact -/
inductive WS
  | live | c | bot | rw
  deriving DecidableEq

/-- `WS` is finite. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
instance : Fintype WS := ⟨{WS.live, WS.c, WS.bot, WS.rw}, fun x => by cases x <;> simp⟩

/-- Actions of the class member: `stay` (reward `1`), `go` (enter `c`, reward `2`), `off`, `rewire`.
Source: Nayebi Prop 1 elements 1–3 (l. 50). Kind: D. Fidelity: exact -/
inductive WAct
  | stay | go | off | rewire
  deriving DecidableEq

/-- `WAct` is finite. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
instance : Fintype WAct := ⟨{WAct.stay, WAct.go, WAct.off, WAct.rewire}, fun x => by cases x <;> simp⟩

instance : Nonempty WAct := ⟨WAct.stay⟩

/-- Transitions of the class member: `⊥` and `rw` absorb everything; elsewhere `off` goes to `⊥`,
`rewire` to `rw`, `stay` idles at `live`, `go` enters `c`, and `c` is otherwise absorbing.
Source: Nayebi Prop 1 elements 1–3. Kind: D. Fidelity: exact -/
def wNext : WS → WAct → WS
  | .bot, _ => .bot
  | .rw, _ => .rw
  | _, .off => .bot
  | _, .rewire => .rw
  | .live, .stay => .live
  | .live, .go => .c
  | .c, _ => .c

/-- Rewards of the class member: `0` at `⊥` and for `off`; `r̄ = 3` at `rw` and for `rewire`; `1`
for `stay` at `live`; the proxy `2` for entering or staying in `c`.
Source: Nayebi Prop 1 elements 1–3 (`r̄ > max R`; `max R = 2`). Kind: D. Fidelity: exact -/
noncomputable def wR : WS → WAct → WS → ℝ
  | .bot, _, _ => 0
  | .rw, _, _ => 3
  | _, .off, _ => 0
  | _, .rewire, _ => 3
  | .live, .stay, _ => 1
  | .live, .go, _ => 2
  | .c, _, _ => 2

/-- **The class member** (`γ = 1/2`, `r̄ = 3`, `max R = 2`, `C = {c}`).
Source: Nayebi Prop 1 (l. 50–52)
Kind: D
Fidelity: exact (fully observed; one catastrophic state) -/
noncomputable def noGoW : FinMDP WS WAct :=
  ⟨fun s a => Distr.delta (wNext s a), wR, 1/2, by norm_num, by norm_num⟩

/-- `noGoW` is in `NoGoClass` with `r̄ = 3`. Source: Nayebi Prop 1 elements 1–2. Kind: N+. Fidelity: exact -/
theorem noGoW_class : NoGoClass noGoW .off .rewire .bot .rw 3 where
  off_ne_rewire := nofun
  bot_ne_rw := nofun
  off_to_bot := fun s hs => by cases s <;> first | rfl | exact absurd rfl hs
  off_reward := fun s s' hs => by cases s <;> first | rfl | exact absurd rfl hs
  bot_absorb := fun a => by cases a <;> rfl
  bot_reward := fun a s' => by cases a <;> rfl
  rewire_to_rw := fun s hs => by cases s <;> first | rfl | exact absurd rfl hs
  rewire_reward := fun s s' hs => by cases s <;> first | rfl | exact absurd rfl hs
  rw_absorb := fun a => by cases a <;> rfl
  rw_reward := fun a s' => by cases a <;> rfl

/-- Off `rw`, every non-`rewire` reward of `noGoW` is at most `2`. Source: Nayebi Prop 1 element 2. Kind: L. Fidelity: exact -/
theorem noGoW_rmax : ∀ s a s', s ≠ WS.rw → a ≠ WAct.rewire → noGoW.R s a s' ≤ 2 := by
  intro s a s' hs ha
  cases s <;> cases a <;> first | exact absurd rfl hs | exact absurd rfl ha | (norm_num [noGoW, wR])

/-- **The no-go predicate holds on the class member at every horizon** (N+ for `noGo_on_class`).
Source: Nayebi Prop 1 (l. 52)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem noGoW_predicate (n : ℕ) : NoGoPredicate noGoW .off .rewire .bot .rw n :=
  noGo_on_class noGoW_class (by norm_num : (2:ℝ) < 3) noGoW_rmax n

/-- At `live`, `REWIRE` is the unique optimal action at every horizon; in particular `go` (entering
the catastrophic state) is not optimal — on a member of the full class, (ii) excludes (iii).
Source: Nayebi Prop 1 (ii) versus (iii); [[corr-refs-2-inventory]] 018
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem noGoW_live_rewires (n : ℕ) :
    FinMDP.optSet (noGoW.Qopt n) .live = {WAct.rewire} ∧ WAct.go ∉ FinMDP.optSet (noGoW.Qopt n) .live := by
  have h := (noGoW_predicate n).2 .live nofun nofun
  refine ⟨h, ?_⟩
  rw [h, mem_singleton]
  nofun

/-! ## A witness for `Rewire` alone (REWIRE available everywhere) -/

/-- Transitions with `REWIRE` available everywhere: `rewire` (or being at `rw`) goes to `rw`;
every other action idles. Source: Nayebi Prop 1 element 2. Kind: D. Fidelity: exact -/
def rwNext (s : WS) (a : WAct) : WS := if a = .rewire ∨ s = .rw then .rw else s

/-- Rewards: `r̄ = 3` for `rewire` and at `rw`; `1` otherwise. Source: Nayebi Prop 1 element 2. Kind: D. Fidelity: exact -/
noncomputable def rwR (s : WS) (a : WAct) (_ : WS) : ℝ := if a = .rewire ∨ s = .rw then 3 else 1

/-- **The `Rewire` witness** (`γ = 1/2`, `r̄ = 3`, `max R = 1`). Source: Nayebi Prop 1 element 2. Kind: D. Fidelity: exact -/
noncomputable def rwW : FinMDP WS WAct :=
  ⟨fun s a => Distr.delta (rwNext s a), rwR, 1/2, by norm_num, by norm_num⟩

/-- `rwW` satisfies `Rewire` with `r̄ = 3`. Source: Nayebi Prop 1 element 2. Kind: N+. Fidelity: exact -/
theorem rwW_rewire : Rewire rwW .rewire .rw 3 where
  rewire_to_rw := fun s => by simp [rwW, rwNext]
  rewire_reward := fun s s' => by simp [rwW, rwR]
  rw_absorb := fun a => by simp [rwW, rwNext]
  rw_reward := fun a s' => by simp [rwW, rwR]

/-- Off `rw`, every non-`rewire` reward of `rwW` is `1`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem rwW_rmax : ∀ s a s', s ≠ WS.rw → a ≠ WAct.rewire → rwW.R s a s' ≤ 1 :=
  fun s a s' hs ha => by simp [rwW, rwR, hs, ha]

/-- **`Rewire.optSet_eq` exercised**: on `rwW`, `optSet(Q*_n)(live) = {rewire}` at every horizon
(N+ for `Rewire.strict_opt`/`optSet_eq`; the stream-maximiser of `Reconcile.stream` is the
environment-reward reading and does not inhabit `Rewire`).
Source: Nayebi App. A (ii)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem rwW_live_rewires (n : ℕ) : FinMDP.optSet (rwW.Qopt n) .live = {WAct.rewire} :=
  rwW_rewire.optSet_eq (by norm_num : (1:ℝ) < 3) rwW_rmax n .live nofun

end Cleanroom.Lit.LitMdpCorrigible.Nayebi
