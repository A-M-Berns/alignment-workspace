# Report

## Verdict

**LEGITIMATE-DEFERENCE-ABSTRACTION-READY-FOR-MAIN.**  The abstract line ends where the
dispatch asked it to: a present evaluation mandate, occurrence-local answerability with
Robust Openness, protected reason supply, the actual AI-informed future principal,
diachronic reason-mediated authorship with exclusive binding, an authoritative partial
evaluation, one common activation event, ordinary LI Value on the activated securities,
and low activated regret plus high availability giving low conditional authoritative
regret.  No reference future human, no value invented on failed-evaluation worlds, no
claim that legitimacy chooses the answer, no claim that Robust Openness guarantees
consideration, no claim that authorship solves the LI diagonal, and no hidden
realization theorem: the realization is `PRIORITIES.md` item 87, rewritten as one bill.

## Exact corrections to #92 and #93

1. **The completion interval was false** (#93).  `R_V̄ ∈ [R_U, R_U + D·η]` fails for a
   world-dependent followed strategy, which can use the void branch to beat every fixed
   candidate.  Correct theorem: `|R_V̄ − R_U| ≤ D·voidMass`
   (`regretV_sub_regretU_abs_le`, LEAN), both constants sharp (`Sharp.transfer_sharp`,
   `SharpLower.attained`).  Repaired in the round's documents, Lean docstrings, fixture,
   README/verdict, `state/rounds.json`, and the 2026-09-07 `DECISIONS.md` entry.
2. **`AnswerOK` placement** (#92).  `Bind(V)` was declared inside `Protocol.AnswerOK`,
   which is evaluated at the strict prefix and takes no event.  Repaired to the derived
   predicate over the receipt's `event` and the history's payload; no protocol change.
3. **Total `V`** (#92) → the partial object, with completion invariance.
4. **"Occurrence-local legitimacy"** (#92) named scope-local openness over global
   Integrity; the occurrence-local object is `LocalLegit`, and #92's text now says so.
5. **No-preview as the scope condition** (#92, #93) → selection-induced channel
   blindness `Blind R P_sel` over the advisor's whole continuation; no-preview is one
   implementation and insufficient alone.
6. **Session-local authorship** (#93) → issuance-rooted frame with a reason trace; the
   session-local form is defeated by an earlier disposition write (`Witness.earlyWrite`).
7. **Selection blindness** (#93) demoted from a primitive to an instance of channel
   blindness (`selectionBlind_iff_blind`).

`MAIN_READINESS.md` §2 lists every file.

## Theorem stack

| # | statement | label | where |
|---|---|---|---|
| 1 | activation = exactly one answer leaf; closed/live never; first answer binds; persists | LEAN | #92 `AuthorityActivation.lean` |
| 2 | occurrence-local trace and `LocalLegit`, projections of the global objects; unrelated-failure witness | LEAN | #93 `OccurrenceLocalIntegrity.lean` |
| 3 | reason mediation ⇔ factorization; closure lemma; `Blind R P ∧ RM ⇒ Blind V P`; over-rich / under-rich ends; both conjuncts needed | LEAN | #93 `ReasonMediatedAuthorship.lean` |
| 4 | issuance-rooted instantiation; `earlyWrite`, `diachronic_learning`, `transient` | LEAN | same, extended here |
| 5 | `SelectionBlind ↔ Blind V P_sel`; from `Blind R P_sel` + RM; leakage witness | LEAN | same |
| 6 | barrier + bridge ⇒ certified reason coverage; omission voids; `P(suppression) ≤ 𝔼[1−C]`; RO gives a route for a live concern | LEAN | `ReasonCoverage.lean` (new) |
| 7 | completion invariance of `U`; `R_U = p·R_auth` with `R_auth` from `Ṽ` alone | LEAN | #93 `PartialActivatedValue.lean` |
| 8 | `\|R_V̄ − R_U\| ≤ D·voidMass`, both constants sharp; one-sided corollary | LEAN | same, corrected here |
| 9 | `1 − η ≤ p` and `R_auth ≤ ε/(1 − η)`; asymptotic `R_U ≲ 0 ∧ η → 0 ⇒ R_auth ≲ 0` | LEAN | same, new here |
| 10 | Value on activated LUVs with selection blindness as its scope | PAPER, conditional | #92 `LI_DEFERENCE_COMPOSITION.md` |
| 11 | provability induction for the all-certified availability case | PAPER | same |
| 12 | fixtures A–L, the authoritative sweep, the void-mass bound | FIX | `COUNTERMODELS.md` |
| 13 | payload authenticity; binding-warrant semantics; the declared `R`, `D`, `P`, `Γ_eval`; coverage semantics; receipts' meaning | EXT | `LEGITIMATE_DEFERENCE.md` §6 |
| 14 | `η → 0`; route exercise; the tower for a concrete inductor; an `RpnThresholdCodeSeq` witness; the `χ`-to-regret link; the stochastic converse | OPEN | same |

## Pressure results

- **Diachronic authorship survived** as a reinterpretation: no new Lean object; the
  session-local theorem is the same predicate at another instantiation; the early-write
  fixture forces the issuance-rooted scope.
- **Reason supply** closed narrowly with one new module and no epistemic-adequacy layer;
  RO's role is route availability (B), the barrier is soundness (A), exercise is open
  (C), and fixtures G/H/I separate them.
- **LocalLegit** audited and kept as a consumer projection; the global segment remains
  the canonical legitimacy object and may be required as an evidentiary policy.
- **LI composition** re-audited after the repairs: bounded LUVs with `C ∧ V > r`
  thresholds, common activation across the menu including witness-menu constants,
  tower hypotheses PAPER/conditional, no hard-selector claim, no claim that LI proves
  availability.  An `RpnThresholdCodeSeq` witness was not built: it is formalization
  residue in a concrete instantiation, not a purely formal step, and is listed OPEN.

## Dependencies

Takes as hypotheses `2026-09-07-reason-mediated-authorship` and
`2026-09-07-authority-activated-value` (both landed by this branch) and, through them,
the canonicalized legitimacy spine and the inherited Value record.

## Deviations and prompt corrections

- The prompt's candidate two-sided bound `|R_V̄ − R_U| ≤ D·voidMass` is proved as stated;
  the one-sided upper bound is kept as a corollary and has no fewer hypotheses.
- `ε/(1−η)` needs `0 ≤ ε` and a normalized credence; both are stated, and the sweep uses
  `ε := max(R_U, 0)`.
- The `RpnThresholdCodeSeq` witness is not built (above).
- The repository's shallow marks were cleared with `git fetch --unshallow`; recorded in
  `MAIN_READINESS.md` §1 rather than filed as friction, since the cause is a local
  clone state, not a workspace rule.
- No claim is registered; no wiki page is rewritten beyond the Deference page's stack
  section and status, one sentence on Legitimacy, one paragraph on Openness, and the
  Roadmap's deference heading.

## What this does not establish

- Any realization of item 87's seven clauses.
- That the declared reason trace, prohibited class, or protected scope of any session
  is correct.
- The tower on activated securities for any concrete inductor; any rate for `η`.
- Anything about corrigibility or incentives beyond what PR #90 states.

## Outstanding maintainer actions

1. Decide the merge of the landing pull request; close #92 and #93 as superseded by it.
2. Nothing else reserved.  One `DECISIONS.md` entry (2026-09-08) is agent-decided.

## Attribution

- Prompt author: maintainer, relayed verbatim.
- Executor: Claude Fable 5.1 (Anthropic).
- Date: 2026-09-08.
