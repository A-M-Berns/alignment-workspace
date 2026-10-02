import Cleanroom.Trust.LegitLiRegister.Defs

/-!
# `legit-li-register` · Open: the recorded open statements of Targets 14 and 15

Two statements the mandate asks to be stated precisely and left open, with their reasons in
`legit-li-register-open.txt`:

* **Target 15** (root-fa-2-008, [[legitimacy-theory-v1]] §2.3, trust-lab-2-032 row (d)): trace
  non-recoverability at the LI register — two frozen-deliberation systems with the same observable
  trace (quotes and verdicts), one with `d_n ≡ 0`, the other with `d_n` bounded away from `0`
  infinitely often. The source labels this THEOREM; the theorem it cites is the finite
  `LegitFiniteDefect.Trace.no_recovery`; at the LI register it is a conjecture (findings F10).
  Route: both must live off `G` (Target 2's certificate forms show the defect vanishes on `G` where
  the pattern is readable); the steered `Hplus'` is `Hplus` with its day-`F n` prices on an
  undecidable contract moved to the quote at infinitely many days, so `perturbAt` (finite support,
  FAF's `thm:ifp`) does not suffice and the route is `li-projection`'s OPEN rewriters
  (`projection_pair_undecidable_contract`'s pattern); `partial: over li-projection's OPEN rewriters`.
* **Target 14** (root-fa-2-013, §2.2 l. 49, §8 item 3): the D3 identification's admissible-domain
  half — "the merged inductor has `d_n → 0` by construction" on every non-quote-referencing family.
  Its negative half is refuted on the diagonal by Target 4 (`defect_ge_half_diagonal`). The
  admissible half is stated over `FrozenSystem` (whose contracts are ledger-free, hence
  non-quote-referencing) as the mandate asks, and left OPEN; the decided fragment of it is Target
  2 (certificate forms). **Note** (findings F11): as stated it quantifies over all days, including
  the undecidable fragment, where T7(ii)'s shape (`li-projection`) makes the horizon price
  underdetermined — so the statement is expected to be *false* off `G`, and its honest form is
  the on-`G` statement, which is Target 2.
-/

namespace Cleanroom.Trust.LegitLiRegister

open LogicalInduction Cleanroom.Deference.DefFrozenSibling
open Filter Topology

/-- **OPEN — trace non-recoverability at the LI register** (Target 15): two frozen-deliberation
systems with the same quotes and the same verdicts, one with zero defect at every day, the other
with the defect at least `δ` infinitely often for some `δ > 0`. The finite theorem is
`LegitFiniteDefect.Trace.no_recovery`; this is its LI-register lift, which the source labels a
theorem without a proof there (findings F10). The shared data are everything but `Hplus` and the
siblings: base and predictor processes, contract, horizon, the three schedules, `A` and the tables
(`DPA0` added after audit round 2 N6). Of the two halves, the `∃ δ, ∃ᶠ` half is the easy one
(a sibling perturbed away from the horizon price on infinitely many days); the hard half is
`defect S ≡ 0` — exact equality of `Hplus (F n) (contract n)` with the sibling's price on
**every** day, for an inductor — which is the mandate's shape and is kept.
Source: root-fa-2-008; [[legitimacy-theory-v1]] §2.3 l. 55–57, §3 row L2; trust-lab-2-032 row (d); audit round 2 (adversarial) N6
Kind: OPEN
Fidelity: variant: the trace as the pair of tables `(a, Y)`; "`liminf d_n > 0`" as "`∃ δ > 0`, frequently `δ ≤ d_n`"
Hyps: n/a -/
theorem trace_nonrecoverable_li_open :
    ∃ S S' : FrozenSystem, S.base = S'.base ∧ S.DPA0 = S'.DPA0 ∧ S.contract = S'.contract ∧
      S.F = S'.F ∧
      S.eq = S'.eq ∧ S.eY = S'.eY ∧ S.σ = S'.σ ∧ S.A = S'.A ∧ S.a = S'.a ∧ S.Y = S'.Y ∧
      (∀ n, defect S n = 0) ∧ ∃ δ : ℝ, 0 < δ ∧ ∃ᶠ n in atTop, δ ≤ defect S' n := by
  sorry

/-- **OPEN — the D3 identification, admissible-domain half** (Target 14, extension): over the
carrier of record (ledger-free contracts), the defect of the accelerator vanishes. Stated as the
mandate asks; expected false off `G` (see the module docstring and findings F11), true on the
timely fragment under a readable pattern (Target 2).
Source: root-fa-2-013; [[legitimacy-theory-v1]] §2.2 l. 49, §8 item 3
Kind: OPEN
Fidelity: variant: "the merged inductor" is the carrier's `A` with `a_eq` (its quote is its expectation of the contract LUV settled to the sibling's verdict); "by construction" rendered as "for every system of the carrier"
Hyps: n/a -/
theorem d3_identification_admissible_open (S : FrozenSystem) (hinj : Function.Injective S.F.f) :
    Tendsto (defect S) atTop (𝓝 0) := by
  sorry

end Cleanroom.Trust.LegitLiRegister
