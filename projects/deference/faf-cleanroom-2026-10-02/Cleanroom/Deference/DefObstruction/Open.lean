import Cleanroom.Deference.DefObstruction.Tracking

/-!
# `def-obstruction` · Open: the package's deliberately open statements

Listed in `run/wp/def-obstruction/def-obstruction-open.txt`; each carries a `sorry` and a
reason. Both are conjectures with a direction; neither is a stalled proof of a source claim.

* `tracking_bound_fails_some_table` — **2a's cost-model certificates are necessary**: for some
  table-only pair and injective deferral, the bound `∀ ε > 0, ∀ᶠ n, ½ − ε ≤ |a 0 n − Y_n|` fails.
  Expected true: a table whose side `𝟙[a 0 n ≤ ½]` is pseudorandom against FAF's trader class
  (values `½` and `1`, say) has, by Learning Pseudorandom Frequencies, `Y_n → ½` along the side,
  so on the side-`1` days (`a 0 n = ½`) the defect tends to `0`. Exhibiting such a table is a
  pseudorandomness construction outside this package (cf. `li-pseudorandom`'s OPEN T7 and
  `li-quote-lane`'s `readability_fails_without_generability`). The settlement defect `|a 0 n − s_n|
  ≥ ½` holds for every table (`exact_defect_table`); only the credence defect needs the
  certificates. Findings F-Oracle.
* `le_diagonal_inductor_exists` — **the `≤`-convention settlement diagonal admits an inductor**:
  some market, process and e.c. family `χ` with `χ_n ↔ (P_n(χ_n) ≤ ½)` in every completed world
  (the ledger's tie-polarity, as `gDiag`'s) and `P` an inductor over `DP`. This is **anson-005's
  own form** (the proposal is written at `≤`; `chiParadox_refuted` refutes the package's `<`
  variant). Expected true (the `<` form is FAF's `ParadoxResistanceQuote` at `½`, inhabited over
  the paper market); FAF has no `≤`-quote package — `paradoxResistanceQuoteOfDiagonal` builds the
  arithmetic fixed point of the comparison `P_n(χ_n) < p` (`parameterizedDiagonalQuoteCodeOfMarket`),
  and the `≤` form needs the fixed point of `¬ (p < P_n(χ_n))`, a parallel construction through
  FAF's quotation layer — and negating a `<`-diagonal moves the price to that of a different
  sentence (`P(∼χ) ≈ 1 − P(χ)` only asymptotically), so it is not a one-line variant. Checked in
  repair round 1: no cheap route (a shifted strict threshold would need a day-varying `p_n → ½`,
  which `ParadoxResistanceQuote` does not take). Findings F-ChiParadox.
-/

namespace Cleanroom.Deference.DefObstruction

open LogicalInduction LO.Propositional Cleanroom.Found.LiQuoteLane Cleanroom.Found.LiAsympCalc
open Cleanroom.Li.LiDiagonal
open Filter Topology

/-- **OPEN (conjectured true): 2a's bound fails for some table.** Some table-only pair and
injective deferral have `¬ (∀ ε > 0, ∀ᶠ n, ½ − ε ≤ |a 0 n − 𝔼^H_{F n}(𝟙 g_n)|)`: the cost-model
certificates of `tracking_fails` are necessary, not decorative. Expected witness: a table with a
pseudorandom side (module docstring).
Scope: one-way.
Source: [[self-referential-settlement-target]] §2.4 ("an oracle for `A` included" — the credence reading, conjectured false); mandate T2 trap (i), T13; findings F-Oracle
Kind: OPEN
Fidelity: exact (the negation of `tracking_fails`'s conclusion, existentially over the carrier)
Hyps: n/a -/
theorem tracking_bound_fails_some_table :
    ∃ (T : TablePair) (F : DeferralFunction), Function.Injective F.f ∧
      ¬ (∀ ε > (0 : ℝ), ∀ᶠ n in atTop, 1 / 2 - ε ≤ |(T.a 0 n : ℝ) - T.Y F n|) := by
  sorry

/-- **OPEN (conjectured true): the `≤`-convention settlement diagonal admits an inductor.** Some
market `P` over a process `DP` with satisfiable stages, and an e.c. family `χ` with
`χ_n ↔ (P_n(χ_n) ≤ ½)` in every completed world, such that `P` is a logical inductor over `DP`.
This is the form anson-005 itself writes (`𝟙[A_n(C_n) ≤ ½]`); the `<` form is
`chiParadox_refuted`'s witness; the `≤` form has no FAF quote package (module docstring).
Scope: single-market.
Source: anson-005 (extension flag), the proposal's own `≤` form; mandate S1 ("the `≤` form … else state OPEN"); findings F-ChiParadox
Kind: OPEN
Fidelity: variant: the diagonal reflection stated directly, without FAF's affine certificates
Hyps: n/a -/
theorem le_diagonal_inductor_exists :
    ∃ (P : History) (DP : DeductiveProcess) (χ : ℕ → Sentence),
      MachineSentenceCodes χ ∧ (∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) ∧
      (∀ n (v : PCWorld), v.ConsistentWithTheory DP → (v.Holds (χ n) ↔ P n (χ n) ≤ 1 / 2)) ∧
      IsLogicalInductor P DP := by
  sorry

end Cleanroom.Deference.DefObstruction
