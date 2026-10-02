import Cleanroom.Bli.BliCoherentMm.AttemptA.Payoffs
import Cleanroom.Bli.BliCoherentMm.AttemptB.Payoffs

/-!
# `bli-coherent-mm` · Payoffs (reconciled): T8, Soto's intermediate payoffs as finite arithmetic

**Of record: attempt B's model** — worlds as Boolean assignments of `n` prime formulas
(`World n := Fin n → Bool`), decision states as partial assignments (`Decision n`), the running
total `payoff W s` (`1/2^(n−k)` for an unrefuted world with `k` confirmations, `0` if refuted),
the increments, and the theorems: **(a)** the running total is the uniform-completion
probability of the world given the decisions (`payoff_eq_uniform`) and Soto's three increment
rules are its differences, so every refinement path telescopes (`sum_increments`); **(b)** once
every prime is decided a world pays `1[true]` and a bundle of `φ`-worlds pays `1[φ]`
(`payoff_full`, `bundle_full`); **(c)** the `½`-forcing per-step inequality (`half_forcing`).
Attempt A formalized the same arithmetic over indices alone (`intermediateTotal n k`, with the
telescoping of `j` confirmations and the bundle identity over `FiniteWorld B` in a decided
state); the identifications are `payoff_eq_intermediateTotal` and `half_forcing_viaA`. Attempt
B's is of record because it models the decision state (so "refuted", "confirmed", "decided"
are defined, not indices), which is what the source's scheme is about.

Disclosed `variant` throughout: PDF 04's scheme is **not** FAF's market (FAF pays by world at
the end); nothing about `Exploits` is claimed. The undecided case — the scheme's failure,
conceded by the source — is a finding, not a theorem. ATTRIBUTION-UNVETTED: the uniform-average
reading and the `½`-forcing are this run's observations, not claims about Soto's intent.

Sources: [[bli-coherent-mm-mandate]] T8, Known issue 7; Soto PDF 04 pp. 1–2 (bli-soto-a-031,
bli-soto-a-2-003).
-/

namespace Cleanroom.Bli.BliCoherentMm.Payoffs

open Finset LogicalInduction LO.Propositional BoolPCWorld Cleanroom.Bli.BliFinite

/-- A world over `n` prime formulas: a Boolean assignment.
Source: Soto PDF 04 ("all possible boolean valuations of these formulas")
Kind: D
Fidelity: variant: prime formulas are indices `Fin n`, not FAF sentences (disclosed) -/
abbrev World (n : ℕ) := AttemptB.Payoffs.World n

/-- A decision state: each prime undecided (`none`) or decided with a truth value.
Source: Soto PDF 04
Kind: D
Fidelity: variant (disclosed) -/
abbrev Decision (n : ℕ) := AttemptB.Payoffs.Decision n

variable {n : ℕ}

/-- `W` is refuted by `s`: some prime is decided against `W`.
Source: Soto PDF 04 ("one of its assignments has already been refuted")
Kind: D
Fidelity: exact -/
abbrev Refuted (W : World n) (s : Decision n) : Prop := AttemptB.Payoffs.Refuted W s

/-- The number of primes decided in agreement with `W` (Soto's `k`).
Source: Soto PDF 04
Kind: D
Fidelity: exact -/
abbrev confirmed (W : World n) (s : Decision n) : ℕ := AttemptB.Payoffs.confirmed W s

/-- **Soto's running total**: a share of `W` has received `1/2^(n−k)` if `W` is unrefuted with
`k` confirmations, and `0` if refuted.
Source: Soto PDF 04 (the immediate payoff rule)
Kind: D
Fidelity: exact (as the running total) -/
abbrev payoff (W : World n) (s : Decision n) : ℚ := AttemptB.Payoffs.payoff W s

/-- Soto's **increment** on deciding prime `i` as `b`: the change of the running total.
Source: Soto PDF 04 (the three rules)
Kind: D
Fidelity: exact -/
abbrev increment (W : World n) (s : Decision n) (i : Fin n) (b : Bool) : ℚ :=
  AttemptB.Payoffs.increment W s i b

/-- The completions of a decision state: the worlds agreeing with every decided prime.
Source: bli-soto-a-2-003 (i) (this run's reading)
Kind: D
Fidelity: n/a -/
abbrev completions (s : Decision n) : Finset (World n) := AttemptB.Payoffs.completions s

/-- **T8(a) (of record). The running total is the uniform-completion probability of the world
given the decisions**: `1 / |completions s|` if `W` completes `s`, else `0`.
Source: [[bli-coherent-mm-mandate]] T8(a); bli-soto-a-2-003 (i) (ATTRIBUTION-UNVETTED reading)
Kind: P
Fidelity: variant (finite arithmetic over indices, not FAF's market)
Hyps: (a) none -/
theorem payoff_eq_uniform (W : World n) (s : Decision n) :
    payoff W s = if W ∈ completions s then 1 / ((completions s).card : ℚ) else 0 :=
  AttemptB.Payoffs.payoff_eq_uniform W s

/-- **T8(a). Every refinement path's increments telescope** to the difference of running totals
(Soto's three rules are exactly the differences of `payoff`).
Source: [[bli-coherent-mm-mandate]] T8(a); Soto PDF 04
Kind: P
Fidelity: variant
Hyps: (a) none -/
theorem sum_increments (W : World n) (s : Decision n) (path : List (Fin n × Bool)) :
    (AttemptB.Payoffs.pathIncrements W s path).sum =
      payoff W (AttemptB.Payoffs.applyPath s path) - payoff W s :=
  AttemptB.Payoffs.sum_increments W s path

/-- **T8(b). Once every prime is decided a world pays its truth**: `1` if it is the decided
world, `0` otherwise.
Source: [[bli-coherent-mm-mandate]] T8(b); Soto PDF 04; bli-soto-a-031
Kind: P
Fidelity: variant
Hyps: (a) `hfull` -/
theorem payoff_full (W : World n) (s : Decision n) (hfull : ∀ i, (s i).isSome) :
    payoff W s = if W = AttemptB.Payoffs.ofFull s hfull then 1 else 0 :=
  AttemptB.Payoffs.payoff_full W s hfull

/-- **T8(b). A share of `φ` — the bundle of `φ`-worlds — totals `1[φ]` once everything is
decided** (Soto's Def 1 bundle reading; the telescoping identity of item 031).
Source: [[bli-coherent-mm-mandate]] T8(b); Soto PDF 04; bli-soto-a-031
Kind: P
Fidelity: variant (`φ` a decidable predicate on assignments; finite arithmetic)
Hyps: (a) `hfull` -/
theorem bundle_full (φ : World n → Prop) [DecidablePred φ] (s : Decision n)
    (hfull : ∀ i, (s i).isSome) :
    ∑ W ∈ univ.filter φ, payoff W s = if φ (AttemptB.Payoffs.ofFull s hfull) then 1 else 0 :=
  AttemptB.Payoffs.bundle_full φ s hfull

/-- **T8(c). The `½`-forcing inequality**: buying the cheaper child at price `θ < 1/2` of a
parent priced `P ≤ 2^{−m}` costs `θ · P`, strictly less than the child's immediate payoff
`2^{−(m+1)}`. A per-step inequality — **not** FAF's `Exploits`.
Source: [[bli-coherent-mm-mandate]] T8(c); bli-soto-a-2-003 (iii) (ATTRIBUTION-UNVETTED)
Kind: P
Fidelity: exact (as the per-step inequality)
Hyps: (a) none -/
theorem half_forcing {θ P : ℚ} (m : ℕ) (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 2) (hP : P ≤ 1 / 2 ^ m) :
    θ * P < 1 / 2 ^ (m + 1) :=
  AttemptB.Payoffs.half_forcing m hθ0 hθ hP

/-! ## Cross-checks with attempt A's index arithmetic -/

/-- **The two attempts' running totals agree**: on an unrefuted world, attempt B's `payoff` is
attempt A's `intermediateTotal n k` at `k := confirmed W s`.
Source: [[bli-coherent-mm-mandate]] §Deliverables (cross-check)
Kind: L
Fidelity: exact -/
theorem payoff_eq_intermediateTotal {W : World n} {s : Decision n} (h : ¬ Refuted W s) :
    payoff W s = AttemptA.intermediateTotal n (confirmed W s) := by
  simp [payoff, AttemptB.Payoffs.payoff, h, AttemptA.intermediateTotal]

/-- **The two attempts' `½`-forcing inequalities agree**: attempt A's `split_cash_inequality`
proves the record's `half_forcing` (the child's payoff `2^{−(m+1)}` is `(1/2)·2^{−m}`).
Source: [[bli-coherent-mm-mandate]] §Deliverables (cross-check)
Kind: P
Fidelity: exact -/
theorem half_forcing_viaA {θ P : ℚ} (m : ℕ) (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 2)
    (hP : P ≤ 1 / 2 ^ m) : θ * P < 1 / 2 ^ (m + 1) := by
  rw [AttemptB.Payoffs.child_payoff]
  exact AttemptA.split_cash_inequality m hθ0 hθ hP

open Classical in
/-- Attempt A's bundle identity over FAF's `FiniteWorld B` in a decided state (the true world
`u₀` totals `1`, every other world `0`): a share of `φ` totals `payoutRat u₀ φ`.
Source: [[bli-coherent-mm-mandate]] T8(b); bli-soto-a-031
Kind: P
Fidelity: variant (decided state only)
Hyps: (a) none -/
theorem bundle_total_decided {B : ℕ} (u₀ : FiniteWorld B) (φ : Sentence) :
    ∑ u ∈ Finset.univ.filter (fun u : FiniteWorld B => (worldOf u).Holds φ),
        (if u = u₀ then (1 : ℚ) else 0) = u₀.payoutRat φ :=
  AttemptA.bundle_total_decided u₀ φ

end Cleanroom.Bli.BliCoherentMm.Payoffs
