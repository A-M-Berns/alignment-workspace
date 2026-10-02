import Cleanroom.Bli.UdtBliTiling.IndepCalc
import Cleanroom.Bli.UdtBliSist.Iterated

/-!
# `udt-bli-tiling` · SingleCoin: the sequential single-coin iterated mugging (T4 model and
verdicts; the file `udt-bli-learning` imports alone)

**Scope: sequential, single coin, finite horizon `K`, one level of tables.** One coin with prior
`q`; `K` rounds; at each round `k`, if the coin is true Omega asks for `c` (the table `Ask_k`), if
false Omega pays `V` iff the policy pays at `Ask_k` (the table `Rec_k`); round weights `γ_k`
("time-penalized" = any positive weights); a residual `r₀ coin` that the policy cannot move.
The base outcome is `(coin, now)`, the table that obtains is `Ask_now` / `Rec_now`, the policy
points are independent uniform (`IndepData`, `prodLaw`), and **the utility sums every round**:
`U₀ (coin, now) π = payoff(coin) · ∑_k γ_k [π Ask_k] + r₀ coin`, `payoff true = −c`,
`payoff false = V`. This is the sequential tree of `udt-bli-sist`'s finding F17 — `{Ask_k, Rec_k}`
is **not** inert at `Ask_k` (the other rounds' points enter every branch) — reusing the index and
tables of `Iter` (`iterIndex`, `iterTables`, `askT`, `recT`) with a different base and utility.
`Other` is a table of the carrier with no mass here (disclosed: `NDHOME` fails at `Other`;
`NDPOL` and `NDPOLICY` hold, every policy is positive, no guard is junk).

Values, all in closed form with `K` symbolic (mandate §3.5, [[plan]] rule 4):
* `exAnteValue_eq`: `𝔼[U | pp = π] = gain · ∑_k γ_k [π Ask_k] + res`, `gain = V(1−q) − cq`;
* `EU_diff` (T4(a), the verdict): `EU Ask_k give − EU Ask_k refuse = γ_k · gain`; one-step pays
  at every round iff `gain > 0` iff `q < V/(V+c)` (`gain_pos_iff`), exact threshold `10/11` at
  `(100, 10)`;
* `twoStepEU_eq`/`twoStep_diff` (the seed of T4(c)): the two-step value at `Σ = {coin}` is the
  coin-true conditional, `twoStepEU Ask_k give − twoStepEU Ask_k refuse = −c · γ_k`;
* `conditionOn_exAnteValue_eq` (T4(d)'s `exAnteValue'`): under the prior re-frozen on the
  coin-true class, `𝔼'[U | pp = π] = −c · ∑_k γ_k [π Ask_k] + r₀ true`;
* `noStrictPrecommit_iff_payOnAsk` (T4(b)): for `gain > 0`, a policy has no strict preference
  for precommitment iff it pays at every `Ask_k` (the one-step optimum is unique at the
  positive-stake tables); `priorOptimal_payAll`.

`LocalUtility` fails here (cross-round terms), so this model is a second instance of T3's
phenomenon — tiling outside T1's package — not an N+ for T1.

Sources: [[bli-program]] §3.9 U9(6); [[bli-program-construction]] X7; [[bli-program-desiderata]]
I10 (Theorem B's model); bli-soto-a-084 (the single-coin iterated mugging), bli-soto-a-2-016/017,
bli-soto-b-038 ("locks in"); mandate T4. Light imports on purpose: `IndepCalc` (hence `Defs`)
and `UdtBliSist.Iterated` only.
-/

namespace Cleanroom.Bli.UdtBliTiling

open Cleanroom.Bli.BliFinite Cleanroom.Bli.UdtBliCore Cleanroom.Bli.UdtBliSist Finset
open Cleanroom.Bli.UdtBliSist.Iter

namespace SingleCoin

/-- **The parameters of the sequential single-coin model**: the coin prior `q ∈ [0,1]`, the
law `w` of the current round, the stakes `c` (asked) and `V` (paid), the round weights `γ`, the
residual `r₀`. Positivity of `c`, `V`, `γ_k`, `q`, `1 − q` is a hypothesis of each theorem that
needs it, never a field.
Source: bli-soto-a-084; [[bli-program-desiderata]] I10; mandate T4 (model)
Kind: D
Fidelity: exact (finite horizon; "time-penalized" = arbitrary positive `γ`) -/
structure Params (K : ℕ) where
  /-- The prior of the coin. -/
  q : ℚ
  /-- `0 ≤ q`. -/
  hq0 : 0 ≤ q
  /-- `q ≤ 1`. -/
  hq1 : q ≤ 1
  /-- The law of the current round. -/
  w : Fin K → ℚ
  /-- `w ≥ 0`. -/
  hw : ∀ k, 0 ≤ w k
  /-- `∑ w = 1`. -/
  hw1 : ∑ k, w k = 1
  /-- The amount Omega asks for. -/
  c : ℚ
  /-- The amount Omega pays. -/
  V : ℚ
  /-- The round weights. -/
  γ : Fin K → ℚ
  /-- The residual, by the coin. -/
  r₀ : Bool → ℚ

variable {K : ℕ}

/-- The base outcome: `(coin, now)`.
Source: mandate T4 (model)
Kind: D
Fidelity: exact -/
abbrev Base (K : ℕ) : Type := Bool × Fin K

/-- The table that obtains: `Ask_now` if the coin is true, `Rec_now` if false.
Source: mandate T4 (model)
Kind: D
Fidelity: exact -/
def baseState (ω : Base K) : ↥(iterTables K) := st K (some ω)

variable (p : Params K)

/-- The base law: `(q or 1 − q) × w now`.
Source: mandate T4 (model)
Kind: D
Fidelity: exact -/
def baseMass (ω : Base K) : ℚ := (if ω.1 then p.q else 1 - p.q) * p.w ω.2

/-- The per-round payoff of paying: `−c` if the coin is true, `V` if false.
Source: bli-soto-a-084 (`(−10, +100)`); mandate T4
Kind: D
Fidelity: exact -/
def payoff (c V : ℚ) (coin : Bool) : ℚ := if coin then -c else V

/-- The weighted number of rounds at which `π` pays: `∑_k γ_k · [π Ask_k]`.
Source: mandate T4 (model)
Kind: D
Fidelity: exact -/
def roundSum (γ : Fin K → ℚ) (π : Policy (iterTables K) Bool) : ℚ :=
  ∑ k, γ k * ind (π (askT K k))

/-- **The utility sums every round**: `payoff(coin) · roundSum γ π + r₀ coin`. Omega reads the
policy point `π Ask_k` at every round in both worlds (mandate T4 traps: no "the agent would have
known" clause).
Source: bli-soto-a-084; bli-soto-b-038; mandate T4 (model: "utility sums all rounds")
Kind: D
Fidelity: exact (the sequential tree of sist's F17) -/
def scU (ω : Base K) (π : Policy (iterTables K) Bool) : ℚ :=
  payoff p.c p.V ω.1 * roundSum p.γ π + p.r₀ ω.1

/-- The base law is nonnegative.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma baseMass_nonneg (ω : Base K) : 0 ≤ baseMass p ω := by
  unfold baseMass
  apply mul_nonneg _ (p.hw ω.2)
  split_ifs
  · exact p.hq0
  · linarith [p.hq1]

/-- Integrating a function of the coin against the base law: `q · f true + (1 − q) · f false`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum_baseMass_mul (f : Bool → ℚ) :
    ∑ ω : Base K, baseMass p ω * f ω.1 = p.q * f true + (1 - p.q) * f false := by
  rw [Fintype.sum_prod_type]
  have hb : ∀ b : Bool, ∑ k : Fin K, baseMass p (b, k) * f b =
      (if b then p.q else 1 - p.q) * f b := by
    intro b
    have e : ∀ k : Fin K, baseMass p (b, k) * f b = p.w k * ((if b then p.q else 1 - p.q) * f b) := by
      intro k; unfold baseMass; ring
    simp only [e]
    rw [← Finset.sum_mul, p.hw1, one_mul]
  simp only [hb, Fintype.sum_bool, ↓reduceIte, Bool.false_eq_true]

/-- The base law has mass one.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma baseMass_sum : ∑ ω : Base K, baseMass p ω = 1 := by
  have := sum_baseMass_mul p (fun _ => 1)
  simp only [mul_one] at this
  rw [this]; ring

/-- Integrating a function of the coin over the coin-true world: `q · f true`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum_baseMass_coin_mul (f : Bool → ℚ) :
    ∑ ω : Base K, (if ω.1 = true then baseMass p ω * f ω.1 else 0) = p.q * f true := by
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, ↓reduceIte, Bool.false_eq_true, Finset.sum_const_zero, add_zero]
  have e : ∀ k : Fin K, baseMass p (true, k) * f true = p.w k * (p.q * f true) := by
    intro k; unfold baseMass; simp only [↓reduceIte]; ring
  simp only [e]
  rw [← Finset.sum_mul, p.hw1, one_mul]

/-- The mass of the coin-true world is `q`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma massOf_coin : massOf (baseMass p) (fun ω : Base K => ω.1 = true) = p.q := by
  unfold massOf
  have := sum_baseMass_coin_mul p (fun _ => 1)
  simp only [mul_one] at this
  exact this

/-- **The single-coin data**: base `(coin, now)` with law `baseMass`, `0/1` faith on `Iter`'s
tables, independent uniform points, the round-summing utility.
Source: mandate T4 (model)
Kind: D
Fidelity: exact -/
def scData : IndepData (iterIndex K) 1 (iterTables K) Bool where
  Ω₀ := Base K
  μ₀ := baseMass p
  μ₀_nonneg := baseMass_nonneg p
  μ₀_sum_one := baseMass_sum p
  state₀ := baseState
  small₀ := fun s φ => decide ((baseState s).1 φ = 1)
  faith₀ := faith_of_zeroOne _ _ (iterTables_zeroOne K)
  ν := prodLaw (half K)
  ν_nonneg := prodLaw_nonneg (fun _ _ => by simp [half])
  ν_sum_one := sum_prodLaw (half_sum K)
  U₀ := scU p

/-- **The sequential single-coin prior** (definition of record; `udt-bli-learning` imports it).
Source: bli-soto-a-084; [[bli-program-desiderata]] I10; mandate T4 (model)
Kind: D
Fidelity: exact (finite horizon, one level) -/
def scPrior : FiniteBLIPrior (iterIndex K) 1 (iterTables K) Bool := (scData p).toPrior

/-- Every policy has positive law.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma ν_pos (π : Policy (iterTables K) Bool) : 0 < (scData p).ν π :=
  prodLaw_pos (fun _ _ => by simp [half]) π

/-- Every point has law `1/2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma massOf_point (T : ↥(iterTables K)) (a : Bool) :
    massOf (scData p).ν (fun π => π T = a) = 1 / 2 := by
  change massOf (prodLaw (half K)) (fun π => π T = a) = 1 / 2
  rw [IndepData.massOf_prodLaw_point (half K) (half_sum K)]
  rfl

/-- **Positivity and the structural predicates of the model**: `NDPOLICY`, `NDPOL`,
`IndependentPoints`, `ReflectivePolicy` (all from the `IndepData` constructor).
Source: mandate T4 (traps: "every policy has positive mass … no guard is junk")
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem structure_facts :
    (scPrior p).NDPOLICY ∧ (scPrior p).NDPOL ∧ (scPrior p).IndependentPoints ∧
      (scPrior p).ReflectivePolicy :=
  ⟨(scData p).ndpolicy_toPrior (ν_pos p),
    (scData p).ndpol_toPrior (fun T a => by rw [massOf_point]; norm_num),
    (scData p).independentPoints_toPrior_of_prodLaw (half K) (half_sum K) rfl,
    (scData p).reflectivePolicy_toPrior⟩

/-! ## The ex-ante value -/

/-- **The per-round gain of paying**: `V(1 − q) − cq`.
Source: bli-soto-a-084 ("pays forever iff `q·100 > (1−q)·10`" — the source's inequality has the
sides of the coin swapped relative to this model's naming; see the findings); mandate T4(a)
Kind: D
Fidelity: exact -/
def gain : ℚ := p.V * (1 - p.q) - p.c * p.q

/-- The expected residual `q · r₀ true + (1 − q) · r₀ false`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def res : ℚ := p.q * p.r₀ true + (1 - p.q) * p.r₀ false

/-- **The ex-ante value of every policy in closed form**:
`𝔼_μ[U | pp = π] = gain · ∑_k γ_k [π Ask_k] + res`.
Source: mandate T4(b)
Kind: P
Fidelity: exact
Hyps: (a) none; does not use faith -/
theorem exAnteValue_eq (π : Policy (iterTables K) Bool) :
    (scPrior p).exAnteValue π = gain p * roundSum p.γ π + res p := by
  unfold scPrior
  rw [IndepCalc.exAnteValue_toPrior (scData p) π (ν_pos p π)]
  change ∑ ω : Base K, baseMass p ω * scU p ω π = _
  unfold scU
  refine (sum_baseMass_mul p (fun b => payoff p.c p.V b * roundSum p.γ π + p.r₀ b)).trans ?_
  unfold payoff gain res
  simp only [↓reduceIte, Bool.false_eq_true]
  ring

/-- `roundSum` is at most the total weight, for nonnegative weights.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma roundSum_le (hγ : ∀ k, 0 ≤ p.γ k) (π : Policy (iterTables K) Bool) :
    roundSum p.γ π ≤ ∑ k, p.γ k := by
  unfold roundSum
  apply Finset.sum_le_sum
  intro k _
  have := ind_le_one (π (askT K k))
  nlinarith [hγ k]

/-- `Ask_k = Ask_j` iff `k = j`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma askT_eq_iff (k j : Fin K) : askT K k = askT K j ↔ k = j := by
  constructor
  · intro h
    have := st_injective K h
    simpa using this
  · rintro rfl; rfl

/-- **One-point update of `roundSum` at `Ask_k`**: `roundSum π[Ask_k ↦ b] = roundSum π +
γ_k · ([b] − [π Ask_k])`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma roundSum_update (π : Policy (iterTables K) Bool) (k : Fin K) (b : Bool) :
    roundSum p.γ (Function.update π (askT K k) b) =
      roundSum p.γ π + p.γ k * (ind b - ind (π (askT K k))) := by
  unfold roundSum
  have e : ∀ j : Fin K, p.γ j * ind (Function.update π (askT K k) b (askT K j)) =
      p.γ j * ind (π (askT K j)) + (if j = k then p.γ k * (ind b - ind (π (askT K k))) else 0) := by
    intro j
    by_cases h : j = k
    · subst h; simp; ring
    · have hne : askT K j ≠ askT K k := fun e => h ((askT_eq_iff j k).mp e)
      simp [hne, h]
  simp only [e, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- The pay-everywhere policy.
Source: bli-soto-b-038 ("pays forever"); mandate T4(d) (`payAll`)
Kind: D
Fidelity: exact -/
def payAll : Policy (iterTables K) Bool := fun _ => true

/-- `roundSum payAll = ∑ γ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma roundSum_payAll : roundSum p.γ (payAll (K := K)) = ∑ k, p.γ k := by
  unfold roundSum payAll; simp

/-- **Paying at every round is prior-optimal** when `gain ≥ 0` and the weights are
nonnegative; strictly better than any policy that refuses at some round with `γ_k > 0` when
`gain > 0`.
Source: bli-soto-a-084 ("the prior-optimal policy pays forever iff …"); mandate T4(b)
Kind: C (`exAnteValue_eq`, `roundSum_le`)
Fidelity: exact
Hyps: (a) `0 ≤ gain`, `0 ≤ γ`; does not use faith -/
theorem priorOptimal_payAll (hg : 0 ≤ gain p) (hγ : ∀ k, 0 ≤ p.γ k) :
    (scPrior p).IsPriorOptimal payAll := by
  intro π
  rw [exAnteValue_eq, exAnteValue_eq, roundSum_payAll]
  have := roundSum_le p hγ π
  nlinarith

/-- **No strict preference for precommitment on the model, characterized**: for `gain > 0` and
positive weights, a policy has no strict preference for precommitment **iff it pays at every
`Ask_k`** — the one-step optimum is unique at every positive-stake table, so a policy tiles iff
its decisions agree with the one-step decisions there (ties only at `Rec_k`/`Other`, where
nothing is at stake). This is the model-level content behind T4(e).
Source: mandate T4(b), T4(e); bli-soto-b-034 D1
Kind: P
Fidelity: exact
Hyps: (a) `0 < gain`, `0 < γ_k`; does not use faith -/
theorem noStrictPrecommit_iff_payOnAsk (hg : 0 < gain p) (hγ : ∀ k, 0 < p.γ k)
    (π : Policy (iterTables K) Bool) :
    NoStrictPrecommit (scPrior p) π ↔ ∀ k, π (askT K k) = true := by
  have hpol := (structure_facts p).1
  constructor
  · intro h k
    by_contra hk
    have hk' : π (askT K k) = false := by simpa using hk
    have hlt : (scPrior p).exAnteValue π <
        (scPrior p).exAnteValue (Function.update π (askT K k) true) := by
      rw [exAnteValue_eq, exAnteValue_eq, roundSum_update, hk']
      simp only [ind_true, ind_false, sub_zero, mul_one]
      nlinarith [hγ k]
    exact not_noStrictPrecommitAt_of_lt (hpol _) hlt (h (askT K k))
  · intro h
    have hsum : roundSum p.γ π = ∑ k, p.γ k := by
      unfold roundSum; apply Finset.sum_congr rfl; intro k _; rw [h k, ind_true, mul_one]
    apply noStrictPrecommit_of_priorOptimal hpol
    intro π'
    rw [exAnteValue_eq, exAnteValue_eq, hsum]
    have := roundSum_le p (fun k => (hγ k).le) π'
    nlinarith

/-! ## The one-step verdict at every round -/

/-- **Conditional moment of a point under the uniform product law**:
`∑_π ν π · [π Q = a] · [π T] = ½ · (if T = Q then [a] else ½)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma condMoment (Q T : ↥(iterTables K)) (a : Bool) :
    ∑ π : Policy (iterTables K) Bool,
        prodLaw (half K) π * ((if π Q = a then (1 : ℚ) else 0) * ind (π T)) =
      1 / 2 * (if T = Q then ind a else 1 / 2) := by
  by_cases hTQ : T = Q
  · subst hTQ
    rw [if_pos rfl]
    cases a
    · have e : ∀ π : Policy (iterTables K) Bool,
          (if π T = false then (1 : ℚ) else 0) * ind (π T) = 0 := by
        intro π; cases h : π T <;> simp [ind]
      simp only [e, mul_zero, Finset.sum_const_zero, ind_false]
    · have e : ∀ π : Policy (iterTables K) Bool,
          (if π T = true then (1 : ℚ) else 0) * ind (π T) = (if π T = true then 1 else 0) := by
        intro π; cases h : π T <;> simp [ind]
      simp only [e]
      rw [sum_prodLaw_mul_ind (half_sum K) T true]
      simp [half]
  · rw [if_neg hTQ]
    have e : ∀ π : Policy (iterTables K) Bool, (if π Q = a then (1 : ℚ) else 0) * ind (π T) =
        (if π Q = a then (1 : ℚ) else 0) * (if π T = true then 1 else 0) := by
      intro π; cases h : π T <;> simp [ind]
    simp only [e]
    rw [sum_prodLaw_mul_ind₂ (half_sum K) (Ne.symm hTQ) a true]
    simp [half]

/-- **The policy-law conditional sum of the utility at `pp · Q = a`**, in closed form:
`½ · (payoff(coin) · ∑_k γ_k · (if Ask_k = Q then [a] else ½) + r₀ coin)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma inner_sum (ω : Base K) (Q : ↥(iterTables K)) (a : Bool) :
    ∑ π : Policy (iterTables K) Bool,
        (if π Q = a then (scData p).ν π * (scData p).U₀ ω π else 0) =
      1 / 2 * (payoff p.c p.V ω.1 * ∑ k, p.γ k * (if askT K k = Q then ind a else 1 / 2) +
        p.r₀ ω.1) := by
  have e : ∀ π : Policy (iterTables K) Bool,
      (if π Q = a then (scData p).ν π * (scData p).U₀ ω π else 0) =
        (∑ k, payoff p.c p.V ω.1 * p.γ k *
          (prodLaw (half K) π * ((if π Q = a then (1 : ℚ) else 0) * ind (π (askT K k))))) +
        p.r₀ ω.1 * (prodLaw (half K) π * (if π Q = a then (1 : ℚ) else 0)) := by
    intro π
    change (if π Q = a then prodLaw (half K) π * scU p ω π else 0) = _
    unfold scU roundSum
    by_cases h : π Q = a
    · simp only [h, if_true, one_mul, mul_one]
      have hs : ∑ k, payoff p.c p.V ω.1 * p.γ k * (prodLaw (half K) π * ind (π (askT K k))) =
          prodLaw (half K) π * (payoff p.c p.V ω.1 * ∑ k, p.γ k * ind (π (askT K k))) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _; ring
      rw [hs]; ring
    · simp [h]
  simp only [e, Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  have h1 : ∀ k : Fin K, ∑ π : Policy (iterTables K) Bool, payoff p.c p.V ω.1 * p.γ k *
      (prodLaw (half K) π * ((if π Q = a then (1 : ℚ) else 0) * ind (π (askT K k)))) =
      payoff p.c p.V ω.1 * p.γ k * (1 / 2 * (if askT K k = Q then ind a else 1 / 2)) := by
    intro k; rw [← Finset.mul_sum, condMoment]
  have h2 : ∑ π : Policy (iterTables K) Bool,
      p.r₀ ω.1 * (prodLaw (half K) π * (if π Q = a then (1 : ℚ) else 0)) = p.r₀ ω.1 * (1 / 2) := by
    rw [← Finset.mul_sum, sum_prodLaw_mul_ind (half_sum K) Q a]; simp [half]
  simp only [h1, h2]
  have h3 : ∑ k, payoff p.c p.V ω.1 * p.γ k * (1 / 2 * (if askT K k = Q then ind a else 1 / 2)) =
      1 / 2 * (payoff p.c p.V ω.1 * ∑ k, p.γ k * (if askT K k = Q then ind a else 1 / 2)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _; ring
  rw [h3]; ring

/-- The round moment at `Q = Ask_j`: `∑_k γ_k (if Ask_k = Ask_j then [a] else ½) =
γ_j ([a] − ½) + ∑_k γ_k/2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma roundMoment_eq (j : Fin K) (a : Bool) :
    ∑ k, p.γ k * (if askT K k = askT K j then ind a else 1 / 2) =
      p.γ j * (ind a - 1 / 2) + ∑ k, p.γ k * (1 / 2) := by
  have e : ∀ k : Fin K, p.γ k * (if askT K k = askT K j then ind a else 1 / 2) =
      (if k = j then p.γ j * (ind a - 1 / 2) else 0) + p.γ k * (1 / 2) := by
    intro k
    by_cases h : k = j
    · subst h; simp; ring
    · have hne : askT K k ≠ askT K j := fun e => h ((askT_eq_iff k j).mp e)
      simp [hne, h]
  simp only [e, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- **The verdict at every round (T4(a))**: `EU Ask_j give − EU Ask_j refuse = γ_j · gain`, with
`gain = V(1 − q) − cq`, by independence of the other rounds' points.
Source: bli-soto-a-084; [[bli-program-desiderata]] I10 Theorem A ("pays at every round iff …");
mandate T4(a)
Kind: P (direct `Finset` algebra over the product law, `K` symbolic)
Fidelity: exact
Hyps: (a) none; does not use faith -/
theorem EU_diff (j : Fin K) :
    (scPrior p).EU (askT K j) true - (scPrior p).EU (askT K j) false = p.γ j * gain p := by
  unfold scPrior
  rw [IndepCalc.EU_toPrior, IndepCalc.EU_toPrior, massOf_point, massOf_point, ← sub_div,
    ← Finset.sum_sub_distrib]
  have e : ∀ ω : Base K, (scData p).μ₀ ω * (∑ π, (if π (askT K j) = true then
        (scData p).ν π * (scData p).U₀ ω π else 0)) -
      (scData p).μ₀ ω * (∑ π, (if π (askT K j) = false then
        (scData p).ν π * (scData p).U₀ ω π else 0)) =
      baseMass p ω * (1 / 2 * (payoff p.c p.V ω.1 * p.γ j)) := by
    intro ω
    rw [← mul_sub, inner_sum, inner_sum, roundMoment_eq, roundMoment_eq]
    change baseMass p ω * _ = _
    simp only [ind_true, ind_false]
    ring
  simp only [e]
  rw [div_eq_iff (by norm_num : (1 / 2 : ℚ) ≠ 0)]
  refine (sum_baseMass_mul p (fun b => 1 / 2 * (payoff p.c p.V b * p.γ j))).trans ?_
  unfold payoff gain
  simp only [↓reduceIte, Bool.false_eq_true]
  ring

/-- **One-step UDT pays at every round when `gain > 0`** (and `γ_j > 0`), uniquely.
Source: bli-soto-a-084; [[bli-program-desiderata]] I10 Theorem A; mandate T4(a)
Kind: C (`EU_diff`)
Fidelity: exact
Hyps: (a) `0 < γ_j`, `0 < gain`; does not use faith -/
theorem isOneStepChoice_pay (j : Fin K) (hγ : 0 < p.γ j) (hg : 0 < gain p) :
    (scPrior p).IsOneStepChoice (askT K j) true ∧
      ¬ (scPrior p).IsOneStepChoice (askT K j) false := by
  have hd := EU_diff p j
  have hpos : 0 < p.γ j * gain p := mul_pos hγ hg
  refine ⟨fun b => ?_, fun h => ?_⟩
  · cases b
    · linarith
    · exact le_rfl
  · have := h true; linarith

/-- **The exact pay threshold**: for positive stakes, `gain > 0 ↔ q < V/(V + c)` (`10/11` at
`(V, c) = (100, 10)`).
Source: bli-soto-a-084 (the inequality, sides named by this model); [[bli-program-desiderata]]
I10 Theorem A (`q < 10/11`); mandate §3.5 (numerics: exact rational)
Kind: P
Fidelity: exact
Hyps: (a) `0 < c`, `0 < V` -/
theorem gain_pos_iff (hc : 0 < p.c) (hV : 0 < p.V) : 0 < gain p ↔ p.q < p.V / (p.V + p.c) := by
  unfold gain
  rw [lt_div_iff₀ (by linarith)]
  constructor <;> intro h <;> nlinarith

/-! ## The two-step value at `Σ = {coin}` -/

/-- The coin price of the table that obtains: `1` iff the coin is true.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma baseState_coin (ω : Base K) : (baseState ω).1 (coin1 K) = if ω.1 then 1 else 0 := by
  rcases ω with ⟨b, k⟩
  exact iterTable_some_coin K b k

/-- `Ask_j` prices the coin `1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma askT_coin (j : Fin K) : (askT K j).1 (coin1 K) = 1 := by
  show iterTable K (some (true, j)) (coin1 K) = 1
  rw [iterTable_some_coin]; simp

/-- **Agreement with `Ask_j` on `{coin}` is "the coin is true"**.
Source: mandate T4(c) ("the class of `Ask_k` is the coin-true tables")
Kind: L
Fidelity: exact -/
lemma agreesOn_coin_iff (j : Fin K) (ω : Base K) :
    agreesOn {coin1 K} (askT K j) (baseState ω) ↔ ω.1 = true := by
  unfold agreesOn
  simp only [Finset.mem_singleton, forall_eq, baseState_coin, askT_coin]
  cases h : ω.1 <;> simp

/-- **The two-step value at `Σ = {coin}` in closed form**: the coin-true conditional,
`twoStepEU {coin} Ask_j a = −c · ∑_k γ_k (if Ask_k = Ask_j then [a] else ½) + r₀ true`.
Source: bli-soto-a-2-016 (`P_σ` with `σ = {coin}`); mandate T4(c)
Kind: P
Fidelity: exact
Hyps: (a) `0 < q`; does not use faith -/
theorem twoStepEU_eq (j : Fin K) (a : Bool) (hq : 0 < p.q) :
    twoStepEU (scPrior p) {coin1 K} (askT K j) a =
      -p.c * ∑ k, p.γ k * (if askT K k = askT K j then ind a else 1 / 2) + p.r₀ true := by
  unfold twoStepEU scPrior
  have hev : ∀ ω : (scData p).Ω₀ × Policy (iterTables K) Bool,
      ((scData p).toPrior.pp ω (askT K j) = a ∧
        agreesOn {coin1 K} (askT K j) ((scData p).toPrior.state ω)) ↔
      (ω.1.1 = true ∧ ω.2 (askT K j) = a) := by
    intro ω
    change (ω.2 (askT K j) = a ∧ agreesOn {coin1 K} (askT K j) (baseState ω.1)) ↔ _
    rw [agreesOn_coin_iff]; exact and_comm
  refine ((condExp_congr _ _ hev).trans
    (IndepCalc.condExp_base_point (scData p) (fun ω₀ : Base K => ω₀.1 = true) (askT K j) a)).trans ?_
  rw [massOf_point]
  change (∑ ω₀ : Base K, if ω₀.1 = true then baseMass p ω₀ * ∑ π, (if π (askT K j) = a then
      (scData p).ν π * (scData p).U₀ ω₀ π else 0) else 0) /
    (massOf (baseMass p) (fun ω₀ : Base K => ω₀.1 = true) * (1 / 2)) = _
  simp only [inner_sum, massOf_coin]
  rw [show (∑ ω₀ : Base K, if ω₀.1 = true then baseMass p ω₀ * (1 / 2 * (payoff p.c p.V ω₀.1 *
      ∑ k, p.γ k * (if askT K k = askT K j then ind a else 1 / 2) + p.r₀ ω₀.1)) else 0) = _ from
    sum_baseMass_coin_mul p (fun b => 1 / 2 * (payoff p.c p.V b *
      ∑ k, p.γ k * (if askT K k = askT K j then ind a else 1 / 2) + p.r₀ b))]
  rw [mul_div_mul_left _ _ (ne_of_gt hq), mul_div_cancel_left₀ _ (by norm_num : (1 / 2 : ℚ) ≠ 0)]
  simp [payoff]

/-- **The two-step verdict at `Σ = {coin}`**: `twoStepEU Ask_j give − twoStepEU Ask_j refuse =
−c · γ_j` — the re-frozen agent refuses at every round, for every `q`, `V`.
Source: bli-soto-a-2-017 (ii) ("`P^(k)` refuses from `t_k` on"); mandate T4(c)
Kind: P
Fidelity: exact
Hyps: (a) `0 < q`; does not use faith -/
theorem twoStep_diff (j : Fin K) (hq : 0 < p.q) :
    twoStepEU (scPrior p) {coin1 K} (askT K j) true -
      twoStepEU (scPrior p) {coin1 K} (askT K j) false = -p.c * p.γ j := by
  rw [twoStepEU_eq p j true hq, twoStepEU_eq p j false hq, roundMoment_eq, roundMoment_eq]
  simp only [ind_true, ind_false]
  ring

/-- **The two-step choice at `Σ = {coin}` is uniquely `refuse`** for `c > 0`, `γ_j > 0`, `q > 0`
(the seed is `udt-bli-sist`'s `Mugging.crux_fails_on_coin`, here at every round).
Source: bli-soto-a-2-016/017; mandate T4(c) ("prove the two-step choice is unique and equals
`refuse`")
Kind: C (`twoStep_diff`)
Fidelity: exact
Hyps: (a) `0 < q`, `0 < c`, `0 < γ_j`; does not use faith -/
theorem isTwoStepChoice_refuse (j : Fin K) (hq : 0 < p.q) (hc : 0 < p.c) (hγ : 0 < p.γ j) :
    IsTwoStepChoice (scPrior p) {coin1 K} (askT K j) false ∧
      ¬ IsTwoStepChoice (scPrior p) {coin1 K} (askT K j) true := by
  have hd := twoStep_diff p j hq
  have hneg : -p.c * p.γ j < 0 := by nlinarith
  refine ⟨fun b => ?_, fun h => ?_⟩
  · cases b
    · exact le_rfl
    · linarith
  · have := h false; linarith

/-! ## The prior re-frozen on the coin -/

/-- **The coin-true class**: the tables pricing the coin `1` (every `Ask_k`).
Source: mandate T4(d) (`coinTrue`)
Kind: D
Fidelity: exact -/
def coinClass (K : ℕ) : Finset ↥(iterTables K) := univ.filter (fun T => T.1 (coin1 K) = 1)

/-- Membership in the coin-true class.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_coinClass_iff (T : ↥(iterTables K)) : T ∈ coinClass K ↔ T.1 (coin1 K) = 1 := by
  simp [coinClass]

/-- The table that obtains is in the coin-true class iff the coin is true.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma baseState_mem_coinClass_iff (ω : Base K) : baseState ω ∈ coinClass K ↔ ω.1 = true := by
  rw [mem_coinClass_iff, baseState_coin]
  cases h : ω.1 <;> simp

/-- **The `{coin}`-class of every `Ask_j` is the coin-true class** (`sigmaClass` of
`udt-bli-sist` = `coinClass`): the re-frozen prior of mandate §3.4 is `conditionOn` at this
class.
Source: mandate §3.4, T4(d)
Kind: L
Fidelity: exact -/
lemma sigmaClass_coin_eq (j : Fin K) : sigmaClass {coin1 K} (askT K j) = coinClass K := by
  ext T
  rw [mem_sigmaClass_iff, mem_coinClass_iff]
  unfold agreesOn
  simp only [Finset.mem_singleton, forall_eq, askT_coin]

/-- The mass of the coin-true class is `q`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma stateClassMass_coinClass : stateClassMass (scPrior p) (coinClass K) = p.q := by
  unfold scPrior
  rw [IndepCalc.stateClassMass_toPrior]
  change massOf (baseMass p) (fun ω₀ : Base K => baseState ω₀ ∈ coinClass K) = p.q
  rw [massOf_congr _ (fun ω₀ => baseState_mem_coinClass_iff ω₀)]
  exact massOf_coin p

/-- The positivity of the coin-true class, from `0 < q`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma coinClass_pos (hq : 0 < p.q) : 0 < stateClassMass (scPrior p) (coinClass K) := by
  rw [stateClassMass_coinClass]; exact hq

/-- **The ex-ante value under the prior re-frozen on the coin** (T4(d)'s `exAnteValue'`):
`𝔼'[U | pp = π] = −c · ∑_k γ_k [π Ask_k] + r₀ true` — the re-frozen prior charges every paid
round and sees no reward.
Source: bli-soto-a-2-017 (ii); mandate T4(d)
Kind: P
Fidelity: exact
Hyps: (a) `0 < q` (through `h`); does not use faith -/
theorem conditionOn_exAnteValue_eq (h : 0 < stateClassMass (scPrior p) (coinClass K))
    (hq : 0 < p.q) (π : Policy (iterTables K) Bool) :
    (conditionOn (scPrior p) (coinClass K) h).exAnteValue π =
      -p.c * roundSum p.γ π + p.r₀ true := by
  unfold scPrior
  rw [IndepCalc.conditionOn_exAnteValue_toPrior (scData p) (coinClass K) h π (ν_pos p π)]
  change (∑ ω₀ : Base K, if baseState ω₀ ∈ coinClass K then baseMass p ω₀ * scU p ω₀ π else 0) /
    massOf (baseMass p) (fun ω₀ : Base K => baseState ω₀ ∈ coinClass K) = _
  rw [massOf_congr _ (fun ω₀ => baseState_mem_coinClass_iff ω₀), massOf_coin]
  simp only [baseState_mem_coinClass_iff]
  unfold scU
  rw [show (∑ ω₀ : Base K, if ω₀.1 = true then
      baseMass p ω₀ * (payoff p.c p.V ω₀.1 * roundSum p.γ π + p.r₀ ω₀.1) else 0) = _ from
    sum_baseMass_coin_mul p (fun b => payoff p.c p.V b * roundSum p.γ π + p.r₀ b)]
  rw [mul_div_cancel_left₀ _ (ne_of_gt hq)]
  simp [payoff]

/-- **The one-step value of the re-frozen prior is the two-step value of the frozen one** at
`Σ = {coin}`: `(P | coinClass).EU Ask_j a = twoStepEU P {coin} Ask_j a`. The re-frozen agent of
mandate §3.4 (the two-step rule at `{coin}`) is one-step UDT over `conditionOn`.
Source: bli-soto-a-2-016 (`P_σ`), mandate §3.4 ("one definition per object")
Kind: L
Fidelity: exact -/
theorem conditionOn_EU_eq_twoStepEU (h : 0 < stateClassMass (scPrior p) (coinClass K))
    (j : Fin K) (a : Bool) :
    (conditionOn (scPrior p) (coinClass K) h).EU (askT K j) a =
      twoStepEU (scPrior p) {coin1 K} (askT K j) a := by
  rw [conditionOn_EU, twoStepEU_eq_classEU, sigmaClass_coin_eq]
  unfold classEU
  apply condExp_congr
  intro ω
  exact and_comm

/-- `Ask_j ≠ Rec_k`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma askT_ne_recT (j k : Fin K) : askT K j ≠ recT K k := fun e => by
  have := st_injective K e
  simp at this

/-- `Ask_j ≠ Other`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma askT_ne_otherT (j : Fin K) : askT K j ≠ otherT K := fun e =>
  Option.some_ne_none _ (st_injective K e)

/-- **At a table no round reads, the re-frozen prior's one-step value is action-blind** (the
utility reads only the `Ask` points): `EU' T a = EU' T b` whenever `T` is no `Ask_k`.
Source: none: infrastructure (ties at `Rec_k` and `Other`)
Kind: L
Fidelity: n/a -/
lemma conditionOn_EU_tied (h : 0 < stateClassMass (scPrior p) (coinClass K))
    (T : ↥(iterTables K)) (hT : ∀ k, askT K k ≠ T) (a b : Bool) :
    (conditionOn (scPrior p) (coinClass K) h).EU T a =
      (conditionOn (scPrior p) (coinClass K) h).EU T b := by
  unfold scPrior
  rw [IndepCalc.conditionOn_EU_toPrior (scData p) (coinClass K) h T a,
    IndepCalc.conditionOn_EU_toPrior (scData p) (coinClass K) h T b]
  simp only [inner_sum, massOf_point, hT, if_false]

end SingleCoin

end Cleanroom.Bli.UdtBliTiling
