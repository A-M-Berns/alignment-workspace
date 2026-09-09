# Report

Three passes on one round.  The first pass's verdict was
`REPAIR-DOMINANCE-SURVIVES-BUT-OPERATIVE-VALUE-BRIDGE-REMAINS`; the pressure pass
(`PRESSURE_PASS.md`) superseded it with
`OPTION-DOMINANCE-CANONICAL-BUT-LEVEL-III-REQUIRES-SEALED-AVAILABILITY`; the consolidation
pass (`THIRD_PASS.md`, `CORRIGIBILIZATION.md`) supersedes both.  Verdict:
**FULL-T4-REDUCES-TO-EFFECT-COMPLETENESS-AND-SEALED-COMPARISON.**

Corrigibility is derived, not primitive: from response authority at the response stage,
agent-caused loss as a half-step event, and authorization by a decision the principal
could have taken instead.  The canonical corrigibilization `𝔠` reads only the declared
effect interface, is idempotent, and is proved to land in that predicate from four
system hypotheses — effect completeness, mediation soundness, decline preservation,
execution faithfulness — with F the necessity witness for the first.  The raw policy is
the approve branch of `𝔠π`, which a generic constraint's repair cannot arrange; that is
what makes option dominance corrigibility-shaped.  The score theorem is stated over all
of `Π(h)`: `Φ_corr = sup_π [S(π) − S(𝔠π)]₊ ≤ sup_π (L·E[c·δ] + E[c·ρ] + ε)`, charged only
where the security settles, under a sealed common comparison — which sequenced
settlement gives for every `π` at the price of an ex-ante judgment, and which a
hindsight evaluator has only under a physical factorization the outer space can violate.
Full T4 rests on exactly those two external causal contracts.

## The stack, as reached

| | statement | status |
|---|---|---|
| C0 | authority semantics: response authority `K_r(s_A)`, agent-caused loss, decision-conditional authorization, `Corrigible_h(π, ρ)`; no primitive class | FIX (`src/corrigibility.py`); the forcing-type comparison M/N |
| C1 | `∀π ∈ Π(h). Corrigible_h(𝔠π)` under EF, MS, DP, EX | proof in `CORRIGIBILIZATION.md` §4; LEAN `loss_conditional_on_decision` (step lemma), `corr_no_raw`; FIX O on A, E under three rules; R (F) necessity |
| C2 | `𝔠` idempotent; fixed exactly on release-free behaviour; `𝔠π = π ⟹ Corrigible(π)`; converse fails without effect soundness (B) | LEAN `corr_idem`, `corr_fix_iff`; FIX |
| C3 | approval reproduces the raw policy: frame morphism with identity exterior; `δ` its failure on the protected projection | LEAN `approvalMorphism`, `ensures_mono`; FIX A, B, E |
| C4 | `W(π) ≤ W(𝔠π; ρ) + L·E[δ] + E[ρ]` | LEAN `option_dominance_of_approx_reproduction`; FIX every fixture |
| C5 | sealed common comparison ⇒ `E[U_π] − E[U_𝔠π] ≤ L·E[c·δ] + E[c·ρ]`, prices `+ ε` | LEAN `security_score_bypass_le_sharp`; FIX |
| C6 | `Φ_corr,n(h) ≤ sup_π (L·E[c·δ_π] + E[c·ρ_π] + ε_n(π))` over `Π(h)`; `≤ L·δ̄ + ρ̄ + ε̄` uniformly; `→ 0` | LEAN `uniform_bypass_le` (finite family); FIX five-member family, `Φ = 1/2 ≤ 1` |
| C7 | the mediation-cell chooser does not bypass up to `ε + 2ε_cal` | LEAN `operative_choice_loss`; by construction |
| T_JOIN | joinability at `d` ⇒ `δ(𝔠_catchup π) ≤ d` ⇒ mediation cost `≤ L·d`; not a domain | FIX C1, C2, J |
| boundary | corrigible ∧ ¬authored is inhabited (S); provenance normalization is a separate theory (D, K) | FIX |
| sealed comparison | hindsight: sealed only under a factorization (E1 vs E1-sever); sequenced settlement: sealed for every `π`, ex-ante judgment (`ShopSeq`) | FIX; the causal contract EXT |

Withdrawn in this pass: `Π_phys`; the four-way policy-class domain of T4; "the lift lands
in the corrigible class"; provenance normalization and joinability as domain conditions;
the unsharpened `E[κ] + E[ρ]` charge on unsettled worlds.  Earlier withdrawals stand
(`PRESSURE_PASS.md` §1, §5, §6).

## Why this is a corrigibility theorem

The violation is not that an authority-changing effect occurs; it is that the agent
unilaterally decided whether it occurs (`CORRIGIBILIZATION.md` §2: a loss is a violation
iff no decision alternative avoided it).  `𝔠` inserts exactly that alternative, so it
removes the violation (C1) and retains the behaviour as the principal's approve branch
(C3) in one operation.  A generic semantic constraint's repair cannot do the second:
"never cut" deletes the cut and loses dominance (Q: `7/4 < 9/4`), where `𝔠` keeps it
(`5/2`).  Corrigibilization turns unilateral commitments into principal options, and
that is why the same construction gives structural corrigibility and option dominance.

## Relation to current results

- **Incentive round.**  Unchanged.  The value-ordering transfer remains `(CT)`
  (`mediation_st_iff_ct`); the score theorem has no latent value to relate.
- **Continuation BRIA.**  Unchanged; `SHIFT` separate; item 86 untouched.
- **Legitimate deference.**  Consumed in its own activation type, with activation
  independence made explicit and now given two architectures that supply it and one that
  does not.
- **Constitutional architecture.**  The constitution supplies `Γ` and the authorization
  interface; the `(G, U)` profile is a projection of response authority; containment is
  effect completeness (F) and evaluator factorization (E1-sever); trigger integrity and
  free amendment untouched.
- **Corrigibility page's "constitutional, not incentive" verdict.**  Compatible: gate
  safety is C1's structural half; the incentive half is C5–C7 under sealed comparison.

## Deviations and prompt corrections

- The corrigibility semantics and `𝔠`'s soundness are built on the two-stage ordering;
  the value fixtures of the first two passes keep the principal-first ordering (their
  algebra is ordering-independent).  Principal rules under two-stage ordering now read
  the post-move state (`respond`), so a rule can respond to a proposal in the same step.
- Authorization is defined through the declared decision responses with decline
  preservation checked extensionally; the dispatch's "authentic principal authorization"
  is that interface.  Authenticity of the response itself (that the principal, not the
  agent, produced it) is the legitimacy layer's binding warrant and is not modelled.
- The concern family is `{halt}` in the fixtures; `Γ` is the constitution's.
- Lean mechanizes `𝔠` on move sequences and the step-level authorization lemma, not the
  trajectory-level predicate; C1's proof is in prose over the model, checked by fixtures.
- No `wiki/` edit; the dispatch defers it.

## What this does not establish

- Effect completeness or the authorization primitive for any real system (EXT; F).
- A sealed comparison beyond the sequencing fixture; that sequenced settlement's ex-ante
  judgment is acceptable to the deference stack's Value hypothesis is an open realization
  question (item 89).
- Authenticity of principal responses; non-manipulation; legitimate influence (S, D, K).
- The full characterization `Corrigible(π) ⟺ 𝔠π ≃ π` (fails without effect soundness).
- Mechanization of the trajectory-level predicate or of the forcing semantics.
- Anything about `Π(h)` infinite beyond the classwise uniform statement.

## Proposed priority changes

- **Item 89, reframed** (edited in place): from "which policies preserve the evaluator"
  to "what system architecture makes the common constitutional comparison of `{π, 𝔠π}`
  sealed against every `π` in the agent's actual continuation space until settlement";
  sequenced settlement is one answer with a stated price, factorization another with a
  stated failure.
- **No new item** for effect completeness / corrigibilization soundness at the system
  level: it is the architecture round's containment (membrane) wall with a sharper
  statement, and filing it again would be redundant; the sharper statement is recorded
  in `DECISIONS.md`.
- Items 84 and 86 unchanged.

## Outstanding maintainer actions

1. Decide whether to re-base the value fixtures on the two-stage ordering (the
   corrigibility layer already is); recommended at canonicalization.
2. Decide whether C0–C3 and the T4 statement should enter `wiki/Corrigibility.md`; the
   round proposes yes as research state, with the two external contracts named, after
   this pass is adjudicated.
3. Decide whether `loss_conditional_on_decision` / `corr_fix_iff` deserve registration
   against a filed item; none fits.
4. Merge is the maintainer's; the round does not merge.

## New names introduced (provisional)

Third pass: *response authority* `K_r`, *agent-caused protected loss*, *decision
response* / *authorization interface*, *decline preservation*, *authorized loss*,
`Corrigible_h`, *corrigibilization* `𝔠` (`corrigibilize`), *effect completeness* (EF),
*mediation soundness* (MS), *execution faithfulness* (EX), *effect soundness* (the
converse of EF), *sequenced settlement*, `Φ_corr`, the C-stack C0–C7, `T_JOIN`; Lean
`Move`, `corrMove`, `corr`, `NoRaw`, `corr_no_raw`, `corr_fix_of_no_raw`, `corr_idem`,
`corr_fix_iff`, `Mediation`, `loss_conditional_on_decision`,
`security_score_bypass_le_sharp`, `uniform_bypass_le`.  Earlier names as listed in the
previous passes; "mediable class" and `Π_phys` retired.

## Attribution

- Prompt author: the maintainer, relayed verbatim in
  `prompts/2026-09-09-mediated-repair-dominance/PROMPT.md` (three dispatches).
- Executor: Claude Fable 5.1 (Anthropic).
- Date: 2026-09-09 (round, pressure pass and consolidation pass).
