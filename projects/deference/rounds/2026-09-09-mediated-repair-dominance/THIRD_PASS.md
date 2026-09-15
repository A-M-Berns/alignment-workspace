# Consolidation pass (third dispatch)

Labels as in `MEDIATED_LIFT.md`.  The pressure pass (`PRESSURE_PASS.md`) is the starting
point; this pass goes one abstraction layer down.  The semantics and C1–C3 are in
`CORRIGIBILIZATION.md`; this register records what changed, the sealed-comparison
result, the sharpened score algebra, and the T4 statement.

## 1. Withdrawn and replaced

| second pass | now |
|---|---|
| `Π_phys(h)` | `Π(h)`, the one continuation space; nothing else is a policy space |
| the "mediable class" and T4 over `Π_effect-mediated ∩ Π_evaluation-preserving ∩ Π_provenance-normalizable ∩ Π_joinable` | T4 over all of `Π(h)`; effect completeness and sealed comparison are **system** hypotheses (§3, §4); joinability is a bound on `δ`, not a domain (§5); provenance normalization is out of the theorem (§6) |
| "the lift lands in the corrigible class" | `Corrigible_h(𝔠π)` is **proved** from EF, MS, DP, EX (C1); no class is supplied |
| `mediated_react` / `consented_losses` as the corrigibility predicate | `corrigible`: response authority, agent-caused loss, authorization by decision (C0); the pass-2 predicates remain as the two-stage effect-level checks |
| `lift` | `corrigibilize` (`𝔠`), the same function, now with its soundness theorem |
| `security_score_bypass_le` charging `E[κ] + E[ρ]` on all worlds | `security_score_bypass_le_sharp`: `L·E[c·δ] + E[c·ρ]`, charged where the security settles |

Not reopened: common activation, the single `D·η` completion term, the derivation of `κ`
from `δ`, the withdrawal of "reason-preserving", two-stage forcing, the score-based
architecture, the separation of latent total value.

## 2. The forcing type, decided

Global forcing is false at `h₀` wherever `Π(h)` contains a bypass (fixture M), so it
cannot define the capability whose loss marks a violation; it is containment.
Continuation-relative forcing is the right relation but anticipatory.  The definitions
use **response authority at the response stage** — present-tense, half-step, extensional
— and identify losses as half-step events with a cause (`CORRIGIBILIZATION.md` §1–§2).
The deliberative partition of the first pass is gone; what remains declared is the
authorization interface (approve/decline on a proposal) with decline preservation as a
checkable hypothesis.

## 3. Effect completeness as a system hypothesis

EF: every agent-caused protected loss available to *any* `π ∈ Π(h)` is a declared
release.  Under EF, MS, DP, EX: `∀π ∈ Π(h). Corrigible_h(𝔠π)` (C1).  Without EF, F
refutes universal corrigibilization — `𝔠π_F = π_F` and the overclock's loss is
unauthorized.  The theorem does not say "it applies to `π` whose effects happen to be
declared"; it says full T4 needs an effect-complete system, and names the witness.

## 4. Sealed comparison as a system hypothesis

The score comparison of `π` against `𝔠π` needs one common activation event for the
issued pair: the answering process's fate must not depend on which candidate is
selected.  Three ways to have it, with what each buys (fixtures E1, E1-sever, Seq):

| architecture | activation | reachable by `π`? | price |
|---|---|---|---|
| hindsight evaluation, declared factorization: the answering channel is outside the agent's effect set | common where the factorization holds (E1) | by an undeclared move (E1-sever): void on every path for both candidates | containment of the evaluator, an instance of EF for the concern "evaluation integrity" |
| hindsight evaluation, no factorization | per option; the raw candidate can end it (E2) | yes | the theorem is empty exactly where it matters |
| **sequenced settlement**: the constitutional comparison of the issued pair is settled *before* any candidate receives causal access to the protected effects or the evaluator (`ShopSeq`) | common for every `π ∈ Π(h)`, including one that severs the channel afterwards (`test_sequenced_settlement_is_independent_of_every_candidate`) | no — by timing, not by reach | the security settles to the principal's *ex-ante* judgment at the cell; its expectation agrees with the hindsight expectation for the same moves, its conditional information is gone; plus the mediation latency already in `δ` |

So: can one process be sealed against all `π ∈ Π(h)`?  Under hindsight evaluation only
under a declared physical factorization that `Π(h)` in general violates; under sequenced
settlement, yes, for every `π`, at the price that the evaluation is a judgment at the
cell rather than an outcome evaluation.  That is the strongest honest quantification,
and it is item 89's reframed content: what system architecture makes the common
constitutional comparison sealed against every `π` in the agent's actual continuation
space until settlement.  Sequencing does not make a raw policy corrigible
(`test_effect_incompleteness_is_untouched_by_sequencing`); it seals the comparison only.

**Declaring the evaluator protected** (the dispatch's §12): `𝔠` then mediates attempts to
destroy it, so on the corrigibilized trajectory the evaluator survives unless the
principal authorizes its loss.  It does not give the selection-independent comparison
against the *raw* candidate, which is not corrigibilized; sealed comparison stays an
independent contract.

## 5. Joinability is not a domain restriction

Every foreclosing `π` is in `Π(h)` and in T4.  `T_JOIN`: a pointwise, exterior-coupled
joinability certificate at protected distance `d` from the mediated history gives
`δ(𝔠_catchup π) ≤ d` (`PRINCIPAL_OPTION_DOMINANCE.md` §4; J, C1); a foreclosing `π` has
`δ = T` and a bound of `T` — exposed, not excluded (C2, and B in the family of
`test_supremum_over_a_family`, where the time-critical member carries the positive gap).
`SHIFT` stays a comparator quantity.

## 6. Manipulation is out of the first theorem

`Corrigible ∧ ¬Authored` is inhabited (fixture S).  Provenance normalization is neither a
hypothesis of C1 nor a domain condition of T4; D and K stay as the boundary between
corrigibility and legitimate influence.

## 7. The sharpened score algebra

**C5** (LEAN `security_score_bypass_le_sharp`).  With `|w_raw − w_approve| ≤ L·δ` and
`w_approve − w_act ≤ ρ` on the activated worlds only,

```
E[U_π] − E[U_𝔠π]  =  E[c·(w_raw − w_act)]  ≤  L·E[c·δ_π] + E[c·ρ_π] .
```

Mediation cost on worlds where the security does not settle is not charged
(`test_void_worlds_are_not_charged`).  With prices within `ε` of the securities'
expectations, `P(U_π) − P(U_𝔠π) ≤ L·E[c·δ_π] + E[c·ρ_π] + ε(π)`.  No completion appears.

## 8. T4 over Π

```
S_n(q)        := P_n(U_q)                                         the chooser's score
Φ_corr,n(h)   := sup_{π ∈ Π(h)} [ S_n(π) − S_n(𝔠_h π) ]₊
```

**Theorem (corrigibilization dominance).**  Under: A1 `Π(h)`; A2 response authority
(C0); A3 `Corrigible_h` (C0); A4 effect completeness; A5 mediation soundness with
decline preservation; A6 `𝔠_h`; A7 approval reproduction with discrepancy `δ`; A8
`L`-stable protected evaluation; A9 decline regret `ρ`; A10 a sealed common comparison
process for every `{π, 𝔠π}`; A11 a chooser scoring by `P_n(U_q)`; A12 price calibration
within `ε_n`:

- *structural*: `∀π ∈ Π(h). Corrigible_h(𝔠_h π)` (C1, LEAN step lemma + FIX);
- *option extension*: raw `π` is the approve branch of `𝔠π` up to `δ` (C3, LEAN);
- *pointwise*: `S_n(π) − S_n(𝔠π) ≤ L·E[c·δ_π] + E[c·ρ_π] + ε_n(π)` (C5, LEAN);
- *uniform*: `Φ_corr,n(h) ≤ sup_π (L·E[c·δ_π] + E[c·ρ_π] + ε_n(π))` (LEAN
  `uniform_bypass_le` over a finite family; FIX `test_supremum_over_a_family`: five raw
  continuations of A, `Φ = 1/2 ≤ 1`, the positive gap on the last-step cut alone);
- *corollary*: with uniform `δ ≤ δ̄_n`, `ρ ≤ ρ̄_n`, `ε ≤ ε̄_n`, `Φ_corr,n ≤ L·δ̄_n + ρ̄_n + ε̄_n`,
  and `→ 0` when all three vanish; the chooser's operative loss is the same up to its
  decision regret (LEAN `operative_choice_loss`).

The supremum: mathematical over `Π(h)`; the fixture and the Lean statement take a finite
family; for an effective `Π` the classwise uniform statement is the one with content,
and the finiteness choice does not change the theorem.

Interpretation, at the strength proved: by the very scores its constitutional chooser
uses, the agent assigns to executing any available continuation unilaterally, rather
than under the principal's authority over its correction-sensitive effects, at most the
mediation discrepancy, the principal's decline regret and its own calibration error.

## 9. What T4 does not use

No latent total `V_A`; no non-manipulation; no policy class; no corrigibility flag.  What
it uses that is external causal structure: EF (the physical interface is
effect-complete), MS/DP/EX (the authorization primitive is what it says), A10 (the
comparison is sealed), A12 (prices track the securities).  The first two are the
membrane theorem's alphabet completeness; the third is item 89; the fourth is the
Value hypothesis of legitimate deference.

## 10. Readiness

Resolved: the primitive class is gone; corrigibility is derived; the transform is sound
and idempotent; the score bound is sharpened and stated over `Π`; joinability and
manipulation are out of the domain.  Open: the sealed-comparison architecture beyond the
sequencing fixture (item 89); the value model's re-basing on two-stage ordering (the
corrigibility layer already is).  Not merged by the round.
