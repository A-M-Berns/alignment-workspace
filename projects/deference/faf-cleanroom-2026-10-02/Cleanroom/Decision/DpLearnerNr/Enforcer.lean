import Cleanroom.Decision.DpLearnerNr.Defs

/-!
# `dp-learner-nr` target 9: the enforcer trader's payoff identity, and VOI = 0 under the proof

**(a) The enforcer** (`enforcer_payoff`): a four-world table (`A = a` or not × the payoff `u` or
`0`); the bundle `V(a)` pays `u` if `A = a` and refunds its price `c` otherwise; the decomposed
bet is one share of `(A = a ∧ U)` plus `q` shares of `¬(A = a)`, priced at `q` in total
(`decomposed_price`); the trader long the bundle and short the decomposed bet has payoff exactly
`q − c` on `A = a` and `0` otherwise, in every world (reversed when `c > q`,
`enforcer_payoff_reversed`). N+: `u = ±10, q = 7/10, c = 3/10 ↦ 2/5` (the note's `4` is at
payoffs scaled by `10`). The LI claim (summability of `|c_t − q_t|` along realized rounds from
non-exploitability) is `li-splice-condition`'s; the refunded bundle is not a FAF `Sentence`
(its world-value depends on its own price), so the FAF statement needs a market extension —
findings.

**(b) VOI = 0 under the proof** (`voi_zero_of_certain`): for a finite `P`, acts `A`, utilities
`U`, and an observation `obs`, `voi := 𝔼_o[max_a 𝔼[U a · 1_o]] − max_a 𝔼[U a]`; with the
observation almost surely constant (the proof pins `P(¬bad ∣ cross) = 0`, so the outcome of
crossing is certain) the post-observation value equals the prior value. `voi_nonneg` is the
standard sign. "VOI of crossing" is this definition — a (c) rendering, disclosed.
-/

namespace Cleanroom.Decision.DpLearnerNr

open Cleanroom.Found.DpCoreTree Cleanroom.Decision.DpCalibration Finset

/-! ## (a) The enforcer trader -/

/-- **The bundle `V(a)`, net of its price `c`**: pays `u` if `A = a` (refunding nothing), and
refunds `c` otherwise — net `u − c` on `A = a`, `0` otherwise.
Source: `Logsidian/journals/2023-05-28.md` l. 20 (as quoted in [[non-responsiveness-learnability]]
§2.1: "A bundle `V(a)` pays `u` if `A = a` and refunds its price `c` if not");
[[dp-core-2-inventory]] 040; [[dp-learner-nr-mandate]] target 9(a)
Kind: D -/
def bundleNet (c u : ℚ) (A : Bool) : ℚ := (if A then u else c) - c

/-- **The decomposed conditional bet, net of its price `q`**: one share of `(A = a ∧ U)` paying
`u·1[A = a]` plus `q` shares of `¬(A = a)` paying `q·1[A ≠ a]`.
Source: [[non-responsiveness-learnability]] §2.1 ("one share of `(A = a ∧ U)` plus `q` shares of
`¬(A = a)` — at `q`"); [[dp-learner-nr-mandate]] target 9(a)
Kind: D -/
def decomposedNet (q u : ℚ) (A : Bool) : ℚ := ((if A then u else 0) + (if A then 0 else q)) - q

/-- The decomposed bet is priced at `q`: with `P(A = a) = pa` and the conditional
`q = 𝔼[U·1_A]/pa`, its price is `pa·q + q·(1 − pa) = q`.
Source: [[non-responsiveness-learnability]] §2.1 ("prices the decomposed conditional bet … at
`q = P(A=a ∧ U)/P(A=a)`"); [[dp-learner-nr-mandate]] target 9(a)
Kind: L -/
theorem decomposed_price (q pa : ℚ) : pa * q + q * (1 - pa) = q := by ring

/-- **The enforcer**: long the bundle, short the decomposed bet.
Source: [[non-responsiveness-learnability]] §2.1 ("goes long the bundle and short the decomposed
bet when `c < q`"); [[dp-learner-nr-mandate]] target 9(a)
Kind: D -/
def enforcerNet (c q u : ℚ) (A : Bool) : ℚ := bundleNet c u A - decomposedNet q u A

/-- **The enforcer's payoff is exactly `q − c` on `A = a` and `0` otherwise, in every world**
(every `u`, every `A`).
Source: [[non-responsiveness-learnability]] §2.1 ("its payoff is `q − c` if `A = a` is realized
and exactly `0` otherwise, in every world"); [[non-responsiveness]] "(i) Conditional contracts";
[[dp-core-2-inventory]] 040; [[dp-core-inventory]] 088(b); [[dp-learner-nr-mandate]] target 9(a)
Kind: L
Fidelity: exact (rational algebra on the four-world table; the LI summability claim is not here)
Hyps: (a) none -/
theorem enforcer_payoff (c q u : ℚ) (A : Bool) :
    enforcerNet c q u A = if A then q - c else 0 := by
  cases A <;> simp [enforcerNet, bundleNet, decomposedNet]

/-- The reversed trade (short the bundle, long the decomposed bet) pays `c − q` on `A = a` and `0`
otherwise — the enforcer's position when `c > q`.
Source: [[non-responsiveness-learnability]] §2.1 ("reversed when `c > q`"); [[dp-learner-nr-mandate]] target 9(a)
Kind: L -/
theorem enforcer_payoff_reversed (c q u : ℚ) (A : Bool) :
    -enforcerNet c q u A = if A then c - q else 0 := by
  rw [enforcer_payoff]; cases A <;> simp

/-- The enforcer's payoff is non-negative in every world when `c ≤ q`, and positive on `A = a`
when `c < q` — the shape that non-exploitability forbids along realized rounds.
Source: [[non-responsiveness-learnability]] §2.1 ("A trader with payoff `≥ 0` in every world and
unbounded cumulative payoff would exploit the market"); [[dp-learner-nr-mandate]] target 9(a)
Kind: L -/
theorem enforcer_nonneg (c q u : ℚ) (hcq : c ≤ q) (A : Bool) :
    0 ≤ enforcerNet c q u A ∧ (c < q → A = true → 0 < enforcerNet c q u A) := by
  rw [enforcer_payoff]
  cases A <;> simp [hcq]

/-- **N+**: `u = ±10`, `q = 7/10`, `c = 3/10` give `2/5` on `A = a` and `0` otherwise (the
note's `4` is at payoffs scaled by `10`).
Source: [[non-responsiveness-learnability]] §8 C ("enforcer payoff when cross, u=+10: 4 …
u=−10: 4 … when not cross: 0"); [[dp-learner-nr-mandate]] target 9(a)
Kind: N+ -/
theorem enforcer_instance :
    enforcerNet (3/10) (7/10) 10 true = 2/5 ∧ enforcerNet (3/10) (7/10) (-10) true = 2/5 ∧
    enforcerNet (3/10) (7/10) 10 false = 0 ∧ enforcerNet (3/10) (7/10) (-10) false = 0 := by
  simp only [enforcer_payoff]; norm_num

/-! ## (b) VOI = 0 under the proof -/

section voi

variable {Ω A O : Type} [Fintype Ω] [Fintype A] [Nonempty A] [Fintype O] [DecidableEq O]

/-- The prior value: `max_a 𝔼_P[U a]`.
Source: [[marginal-formula-learner]] "Why VOI alone does not rescue EDT"; [[dp-learner-nr-mandate]] target 9(b)
Kind: D -/
def priorValue (P : FinDistr ℚ Ω) (U : A → Ω → ℚ) : ℚ :=
  univ.sup' univ_nonempty fun a => ∑ ω, P.w ω * U a ω

/-- The post-observation value: `∑_o max_a 𝔼_P[U a · 1_{obs = o}]` — the textbook
`∑_o P(o)·max_a 𝔼[U a ∣ o]` with the `P(o)` factors cancelled (so a null `o` contributes `0`,
no junk division).
Source: [[dp-learner-nr-mandate]] target 9(b) ("`𝔼[max_a' 𝔼[U ∣ a', obs]] − max_a' 𝔼[U ∣ a']`")
Kind: D
Fidelity: variant: the `P(o)`-weighted conditional expectations written as unnormalized
fiber sums -/
def postValue (P : FinDistr ℚ Ω) (U : A → Ω → ℚ) (obs : Ω → O) : ℚ :=
  ∑ o, univ.sup' univ_nonempty fun a => ∑ ω ∈ univ.filter (fun ω => obs ω = o), P.w ω * U a ω

/-- **The value of information** of observing `obs` before choosing among `A`.
Source: [[marginal-formula-learner]] ("the information value of crossing"); [[dp-core-inventory]]
088(b); [[dp-learner-nr-mandate]] target 9(b)
Kind: D
Fidelity: variant: "VOI of crossing" is rendered as the VOI of observing the outcome `obs` —
a (c) rendering, disclosed -/
def voi (P : FinDistr ℚ Ω) (U : A → Ω → ℚ) (obs : Ω → O) : ℚ := postValue P U obs - priorValue P U

/-- VOI is non-negative: `max_a ∑_o S_a(o) ≤ ∑_o max_a S_a(o)`.
Source: none: infrastructure (the standard sign)
Kind: P -/
theorem voi_nonneg (P : FinDistr ℚ Ω) (U : A → Ω → ℚ) (obs : Ω → O) : 0 ≤ voi P U obs := by
  unfold voi postValue priorValue
  rw [sub_nonneg]
  apply Finset.sup'_le
  intro a _
  rw [← Finset.sum_fiberwise univ obs (fun ω => P.w ω * U a ω)]
  apply Finset.sum_le_sum
  intro o _
  exact Finset.le_sup' (fun a => ∑ ω ∈ univ.filter (fun ω => obs ω = o), P.w ω * U a ω) (mem_univ a)

/-- Off an almost-sure event the weights vanish. Source: none: infrastructure. Kind: L -/
theorem weight_zero_off [DecidableEq Ω] (P : FinDistr ℚ Ω) (S : Finset Ω) (h : probOf P S = 1) (ω : Ω)
    (hω : ω ∉ S) : P.w ω = 0 := by
  have hsplit : probOf P S + probOf P Sᶜ = 1 := by
    rw [← probOf_union P disjoint_compl_right, Finset.union_compl, probOf_univ]
  have hc : probOf P Sᶜ = 0 := by linarith
  unfold probOf at hc
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun ω _ => P.nonneg ω)).mp hc ω (Finset.mem_compl.mpr hω)

/-- **VOI = 0 under the proof**: if the observation is almost surely `o₀` — under the proof
`P(¬bad ∣ cross) = 0`, so the outcome of crossing is certain — then the post-observation value
is the prior value and the information value is zero.
Source: [[marginal-formula-learner]] ("With the proof in hand a proof-respecting conditional has
`P(¬bad | cross) = 0`, so the information value of crossing is exactly zero");
[[dp-core-inventory]] 088(b); [[dp-learner-nr-mandate]] target 9(b)
Kind: P
Fidelity: variant: (c) "VOI of crossing" rendered as the VOI of an almost-surely constant
observation. The source's claim is *conditional* — certainty of the outcome *given crossing* —
and `voi` has no conditioning on the act: the rendering keeps only the unconditional consequence
(the observation is a.s. constant), which makes this the generic "a constant observation has no
value" (`voi_const_obs_zero`); `voi` itself is not identically zero (`voi_pos_instance`)
Hyps: (c) the rendering of "VOI of crossing" as `voi`; (a) `P(obs = o₀) = 1` -/
theorem voi_zero_of_certain [DecidableEq Ω] (P : FinDistr ℚ Ω) (U : A → Ω → ℚ) (obs : Ω → O) (o₀ : O)
    (h : probOf P (univ.filter fun ω => obs ω = o₀) = 1) : voi P U obs = 0 := by
  have hS : ∀ a, ∑ ω ∈ univ.filter (fun ω => obs ω = o₀), P.w ω * U a ω = ∑ ω, P.w ω * U a ω := by
    intro a
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun ω _ => ?_
    split_ifs with hω
    · rfl
    · rw [weight_zero_off P _ h ω (by simpa using hω)]; ring
  have hoff : ∀ o, o ≠ o₀ → ∀ a, ∑ ω ∈ univ.filter (fun ω => obs ω = o), P.w ω * U a ω = 0 := by
    intro o ho a
    apply Finset.sum_eq_zero
    intro ω hω
    have hω' : ω ∉ univ.filter (fun ω => obs ω = o₀) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
      rw [hω]; exact ho
    rw [weight_zero_off P _ h ω hω']; ring
  unfold voi postValue priorValue
  rw [Finset.sum_eq_single o₀]
  · rw [sub_eq_zero]
    congr 1
    funext a
    exact hS a
  · intro o _ ho
    have : (fun a => ∑ ω ∈ univ.filter (fun ω => obs ω = o), P.w ω * U a ω) = fun _ => (0 : ℚ) := by
      funext a; exact hoff o ho a
    rw [this, Finset.sup'_const]
  · intro h'; exact absurd (Finset.mem_univ o₀) h'

/-- **`voi_zero_of_certain` is the generic fact "a constant observation has no value"**: every
constant observation on every `P`, `U` has `voi = 0`. Stated so the reader sees that the
source's *conditional* claim (`P(¬bad ∣ cross) = 0` — certainty *given crossing*) is rendered
by its unconditional consequence (certainty of `obs`); the conditioning on crossing is not
modelled by `voi`. Adopted from audit r1's `VoiGeneric` probe.
Source: [[dp-learner-nr-audit-r1-adversarial]] §3 item 7; [[dp-learner-nr-mandate]] target 9(b)
Kind: L
Hyps: (c) the rendering of "VOI of crossing" as `voi` -/
theorem voi_const_obs_zero [DecidableEq Ω] (P : FinDistr ℚ Ω) (U : A → Ω → ℚ) (o₀ : O) :
    voi P U (fun _ => o₀) = 0 := by
  apply voi_zero_of_certain P U (fun _ => o₀) o₀
  have : (univ.filter fun _ : Ω => o₀ = o₀) = univ := by simp
  rw [this]
  exact probOf_univ P

end voi

/-! ### VOI is not identically zero: a guessing game -/

/-- A guessing game: act `a` pays `1` iff `a = ω`. Source: none: infrastructure. Kind: D -/
def voiGuess : Bool → Bool → ℚ := fun a ω => if a = ω then 1 else 0

/-- The fair coin on `Bool`. Source: none: infrastructure. Kind: D -/
abbrev voiFair : FinDistr ℚ Bool := boolDistr (1/2) (by norm_num) (by norm_num)

/-- The per-observation fiber sums of `postValue voiFair voiGuess id`.
Source: none: infrastructure. Kind: D -/
def voiFiber (o : Bool) : Bool → ℚ :=
  fun a => ∑ ω ∈ univ.filter (fun ω : Bool => id ω = o), voiFair.w ω * voiGuess a ω

/-- `voiFiber true true = ½`. Source: none: infrastructure. Kind: L -/
theorem voiFiber_true : voiFiber true true = 1 / 2 := by
  norm_num [voiFiber, voiGuess, Finset.sum_filter, Fintype.sum_bool]

/-- `voiFiber false false = ½`. Source: none: infrastructure. Kind: L -/
theorem voiFiber_false : voiFiber false false = 1 / 2 := by
  norm_num [voiFiber, voiGuess, Finset.sum_filter, Fintype.sum_bool]

/-- **N+: `voi` is not identically zero** — observing `ω` itself in the fair guessing game has
information value `≥ ½ > 0` (the prior value is `½`, the post-observation value is `1`). So
`voi_zero_of_certain` is not an artifact of a degenerate definition. Adopted from audit r1's
`VoiGeneric` probe.
Source: [[dp-learner-nr-audit-r1-adversarial]] §3 item 7; [[STANDARDS]] §3 (non-vacuity)
Kind: N+ -/
theorem voi_pos_instance : 0 < voi voiFair voiGuess id := by
  unfold voi
  have hprior : priorValue voiFair voiGuess ≤ 1 / 2 := by
    unfold priorValue
    apply Finset.sup'_le
    intro a _
    cases a <;> norm_num [voiGuess, Fintype.sum_bool]
  have hpost : 1 ≤ postValue voiFair voiGuess id := by
    have hT : voiFiber true true ≤ univ.sup' univ_nonempty (voiFiber true) :=
      Finset.le_sup' (voiFiber true) (mem_univ true)
    have hF : voiFiber false false ≤ univ.sup' univ_nonempty (voiFiber false) :=
      Finset.le_sup' (voiFiber false) (mem_univ false)
    rw [voiFiber_true] at hT
    rw [voiFiber_false] at hF
    show 1 ≤ ∑ o, univ.sup' univ_nonempty (voiFiber o)
    rw [Fintype.sum_bool]
    linarith
  linarith

end Cleanroom.Decision.DpLearnerNr
