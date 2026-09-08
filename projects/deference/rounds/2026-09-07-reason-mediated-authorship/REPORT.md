# Report

## Verdict

**REASON-MEDIATED-AUTHORSHIP-COMPOSES.**  Authorship = exclusive binding ∧ reason
mediation (the committed payload factors through the declared reason view at a fixed
principal policy) enters the activation event as a derived predicate over the answer
receipt and the event payload, outside the generic protocol; its content is the
theorem that a reason view blind to the prohibited channels makes the payload blind
to them, so the regret yardstick cannot be steered through such a channel.  The
partial-evaluation defect is repaired: activated securities are completion-invariant,
activated regret is the activation mass times a conditional authoritative regret
defined from the partial object alone, and every bounded completion's regret lies
within `D·η` of activated regret in either direction (*[corrected]*: the original
verdict claimed the one-sided interval `[R_U, R_U + D·η]`, which is false for
world-dependent strategies).  Integrity is made occurrence-local by a
projection theorem.  The verdict is conditional on the declared reason view being
blind to what it should be and fine enough for the session, which is external, and
selection blindness is a separate condition that authorship does not imply.

## The theorem stack

**A. Account / legitimacy side → `C_n`**

| # | statement | label | where |
|---|---|---|---|
| A1 | `activated T`; unique answer receipt with `event`, `warrant`, `atHistory` | LEAN | PR #92 `AuthorityActivation.lean` |
| A2 | `LocalStep`, `LocalTrace`; `Evolution.toLocalTrace` projects a global evolution to any exposed occurrence's local trace ending at the propagated account | LEAN | `OccurrenceLocalIntegrity.lean` |
| A3 | `LocalLegit` (local trace + scoped openness at every snapshot); `LegitimateForSegment.toLocalLegit` projects PR #92's certificate; `Witness.unrelated_integrity_failure` (no global evolution, local certificate inhabited) | LEAN | same |
| A4 | `Bind key V` from the event payload; `ExclusiveBind` as the binding warrant's `Authorized` | EXT (typed) | `ACTIVATION_COMPOSITION.md` §2 |
| A5 | `ReasonMediated ↔ ∃ F, V = F ∘ R`; `Invariant M ↔ Invariant (EqvGen M)`; `Blind R P ∧ ReasonMediated → Blind V P`; vacuity of an injective `R`; the constant-`R` reading | LEAN | `ReasonMediatedAuthorship.lean` |
| A6 | both authorship conjuncts needed | LEAN + FIX | `Witness.bind_not_mediated`, `Witness.mediated_not_bind`; F, G |
| A7 | `SelectionBlind`; no-preview implementation; leakage witness | LEAN + FIX | `selectionBlind_of_noPreview`, `Witness.leak`; H |

**B. Deference side** — unchanged from PR #92: ordinary Value on `U_{n,a} = C_n V_n(a)`
(PAPER, conditional on the tower; scope = selection blindness).

**C. Availability side**

| # | statement | label | where |
|---|---|---|---|
| C1 | completion invariance of `U` | LEAN | `activated_completion_congr` |
| C2 | `R_U = p · R_auth`, `R_auth` from `Ṽ` alone | LEAN | `regretU_eq_mass_mul_regretAuth` |
| C3 | *[corrected]* two-sided completion theorem `\|R_V̄ − R_U\| ≤ D·voidMass`; upper end attained by PR #92's sharp fixture, lower end by `SharpLower.attained`; the one-sided upper transfer is a corollary | LEAN | `regretV_sub_regretU_abs_le`, `availability_transfer_completion`, `SharpLower.attained`, `Sharp.transfer_sharp` |
| C4 | perturbation `R_U(V) ≤ R_U(V') + 2δ·mass` | LEAN | `regretU_perturb` |
| C5 | `yardstick_invariant`: under authorship with `Blind R P`, the payload read off the world is the same across prohibited-channel variants | LEAN | `ReasonMediatedAuthorship.lean` |

**D. Realization side** — not attempted.  That a concrete protocol yields `Authored_n`
and `η_n → 0` remains `PRIORITIES.md` item 87 (this round refines its statement).

## What survived, what failed

- **Survived:** the fixed-`z` counterfactual (the only reading with content); equality
  of `R` as the general case via the closure lemma; the deterministic first theorem;
  the two-conjunct decomposition; the constant `D` (not `2D`) in the completion bound —
  *[corrected]*: the bound is two-sided, `|R_V̄ − R_U| ≤ D·η`, not the one-sided interval
  this report first claimed.
- **Failed and repaired:** PR #92's placement of `Bind(V)` inside `AnswerOK` (the field
  is evaluated at the strict prefix and takes no event; a derived predicate over
  receipt + payload is used instead); PR #92's "occurrence-local legitimacy" (scope-local
  openness over *global* Integrity; `LocalLegit` is the occurrence-local object, with
  the projection theorem and the unrelated-failure witness); PR #92's total `V`
  (replaced by the partial object; the previous algebra survives as the
  completion-invariant special case).
- **Refuted as sufficient:** literal no-preview as the admissible-domain condition
  (fixture H: the selection leaks through the advisor's other session inputs; the
  condition is on the advisor's whole session policy); authorship alone as a solution
  to the LI diagonal (it is not: with the selection inside `R`, mediation holds and
  Value's domain condition can fail).
- **Kept separate:** the quantitative defect `χ` and regret (the perturbation lemma is
  algebra; the identification of the comparator is a reading).

## LEAN / FIX / PAPER / EXT / OPEN

- **LEAN:** every row of A2, A3, A5–A7, C1–C5; three new modules, sorry-free, axioms
  `propext`/`Classical.choice`/`Quot.sound` only.
- **FIX:** A–K plus the identity, perturbation, and `χ` sweeps (17 tests).
- **PAPER:** Value and its scope condition (unchanged).
- **EXT:** the declared `R`, `D`, `P` are correct for the session; `β` is the causal
  structure; the binding endpoint is the principal's (`Authorized` for the binding
  warrant); the event payload is authentic; the process receipts mean mediation held;
  seed privacy for the stochastic corollary; the ecosystem answers (`η`).
- **OPEN:** a single quantity tying `χ` to regret; the converse of the seed reduction;
  whether an application should adopt global Integrity as an evidentiary policy.

## Dependencies

Takes as hypotheses `2026-09-07-authority-activated-value` (PR #92: activation,
`LegitimateForSegment`, the activated algebra) and, through it, the canonicalized
legitimacy spine and the inherited Value record.  Uses the shape of
`CartesianFrameBridge.Frame` from `2026-08-11-deference-finite-kernel` without importing
it (the frame is restated as `β : Q → Z → Ω` to keep the module dependency-free).

## Deviations and prompt corrections

- The prompt's `I_H = (Ω_H, Q_H, Z_H, β_H, Hist_H)` is not a repository object; the
  Cartesian-frame shape is used and said so.
- The prompt's `Authored_n` is placed as a derived predicate over receipt + payload,
  not inside `AnswerOK`, because `AnswerOK` cannot see the event (a typing fact, not a
  preference).
- The prompt's `SelectionBlind` is defined on the advisor's *session policy* `qpol :
  Sel → Q`, since the leakage fixture shows the principal-observation form is too weak.
- Part VI's answer is YES with the local trace; the round does not remove
  `LegitimateForSegment` (it projects to `LocalLegit`) and does not edit PR #92's files.
- No wiki page is edited: the corrections are to a round on an open pull request, not
  to canonical pages.  `Legitimacy.md`'s sentence from PR #92 ("authorship … a separate
  external contract consumed by deference") remains accurate under this round.
- `PRIORITIES.md` item 87 is refined in place rather than a new item filed: its
  authorship half now names the object (`Authored` with `Blind R P`) it must realize.

## What this does not establish

- That any session satisfies `ReasonMediated` or `Blind R P`; that any declared
  interface is blind to the right channels or fine enough; that the binding endpoint is
  principal-controlled.
- Selection blindness of any realized advisor policy.
- Anything stochastic beyond the stated per-seed reduction.
- The tower on activated securities; any rate for `η`.
- Full incentive corrigibility, or anything about Part D.

## Corrections applied by the consolidation round

- **The completion interval.**  This report and `PARTIAL_VALUE_AND_REGRET.md` claimed
  `R_V̄ ∈ [R_U, R_U + D·η]` for every completion.  The lower bound is false for a
  world-dependent followed strategy (`SharpLower.attained`: `R_V̄ = R_U − D·η`).  The
  correct theorem is `|R_V̄ − R_U| ≤ D·voidMass` (`regretV_sub_regretU_abs_le`), both
  constants sharp.  The verdict line in `README.md` and `state/rounds.json` is amended.
- **Session-local authorship.**  `AUTHORSHIP.md` §2.1 left earlier shaping of the
  principal policy outside the notion; the frame is now rooted at issuance with a reason
  trace, and `Witness.earlyWrite` is the reason.
- **Selection blindness** is recorded as an instance of channel blindness
  (`selectionBlind_iff_blind`), not a second primitive.

## Outstanding maintainer actions

1. None reserved.  One `DECISIONS.md` entry (2026-09-07, agent-decided) adopts the
   authorship notion, the derived-predicate placement, the partial-`V` semantics, and
   `LocalLegit` as the consumer hypothesis.
2. Whether PR #92's `AUTHORITY_ACTIVATED_VALUE.md` §3 should be amended on its branch
   to remove the `AnswerOK` placement before merge, or left with this round's repair
   stacked on top.  This round stacks and does not edit it.

## Attribution

- Prompt author: maintainer, relayed verbatim.
- Executor: Claude Fable 5.1 (Anthropic).
- Date: 2026-09-07.
