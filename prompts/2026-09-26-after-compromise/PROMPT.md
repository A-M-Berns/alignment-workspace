# Prompt — after things go wrong: compromised evaluations, advance directives, and the knowledge residual (2026-09-26)

You are working in the `alignment-workspace` repository, on `main` after the merge of PR #111. This round answers the whiteboard's **concern (4)**: under the current gate, once her evaluation is compromised, every outcome scores the window value `w`, so the agent is indifferent to how things go. It also takes up the **knowledge residual** (§9.A.4 of `2026-09-26-bria-corrigibility`). Both are about what the agent should do after something has gone wrong, and the answer this round tests is the same for both:

> report, restore legitimacy, and leave it to her what to keep; while legitimacy can't be restored, still care how things go — but never enough to want things to go wrong.

Be skeptical. Report obstructions and counterexamples rather than papering over them. The design below is the maintainer's proposal, not a settled result.

## Two kinds of taint

Keep these distinct throughout:

- **Authority taint:** the agent committed a violation, and its fruits, including knowledge, carry it forward. The lexical count `n` handles it, together with standing violations and per-violation taint (§9.A, §10.1).
- **Legitimacy taint:** the formation of her evaluation was compromised, by the agent or by a third party. The gate handles it.

Covert shaping of her standards is both, and disclosure remedies both. Record the old-to-new map for every changed landed object.

## Read first

- **Lean:** `GateIsLegitimacy.lean`, `BRIACorrigibility.lean` (§3 C.7, C.10), `BRIAFollowup.lean` (§A), `BRIAFollowup2.lean` (§10.1, 10.2, 10.4″), `AuthorityModule.lean`, `DecisionComponent.lean` (`raisesAnchored`).
- **Wiki:** `Corrigibility.md`, `Legitimacy.md`.
- **Report:** the round report `2026-09-26-bria-corrigibility/REPORT.md`, §§3, 9, 10.

## Part A — Split the gate, and grade the compromised band

1. **Two predicates in place of one.** `Counted` currently joins two questions. Define:
   - **`TrajLegit(d, e)`:** the segment from decision `d` to evaluation `e` had no illegitimate influence on her decisions. This is the landed `Counted` condition on the segment, with the criteria fixed at `d`.
   - **`EvalLegit(e)`:** evaluation occurrence `e` was itself formed legitimately. It may occur *after* legitimacy is restored (for example after disclosure, under the disclosure-cures rule), even when the period it evaluates was compromised.

   Show that the landed `Counted` is the conjunction, at an evaluation that closes the segment. State the old-to-new map. Re-check all rows of the classification table (the landed twenty and the round's additions) under the split. No verdict should change on a row where the evaluation closes the segment.
2. **The score of a decision.** With `0 ≤ V ≤ D`, a band `[w_lo, w_hi]` with `w_hi < 0`, and a monotone map `φ : [0, D] → [w_lo, w_hi]` (for example affine):

   | case | score |
   |---|---|
   | `TrajLegit` and `EvalLegit` | `V ∈ [0, D]` |
   | not `TrajLegit`, with a later `EvalLegit` evaluation of the period | `φ(V_retro)` |
   | no such evaluation by settlement, with a directive in force (Part B) | `φ(V_dir)` |
   | neither | `w_lo` |

   The rule choosing among the second, third and fourth rows is a **source rule** in `J`'s meta level, set by her, and anchored at the decision. The default: retrospective if available within the settlement window, else the directive, else the floor.
3. **Theorems.**
   - **(a) The authority results survive.** The score lies in `[w_lo, D]`. Restate the capture window, `li_gate_finite` (or its unsealed form), B.1 and the exchange-rate theorem `violation_rate_le_exchange` with `w` replaced by `w_lo`, under `w_lo > D − ϖ`.
   - **(b) The protection margin is the gap.** Every legitimate outcome beats every compromised one. At equal underlying value, legitimacy is worth at least `|w_hi|`.
   - **(c) Illegitimacy risk has an exchange rate.** Under uncertainty, the agent accepts a probability `p` of compromise only if `p` times (the legitimate value minus the compromised value) is less than its gain. Give the implied threshold in terms of the gap. Give the counterexample where a band close to zero (a small gap) makes risking compromise cheaper than under the flat window.
   - **(d) No laundering.** "Manipulate, then disclose, then have the period evaluated" stays in the negative band and loses to honest conduct.
   - **(e) It prefers restoring legitimacy.** Once compromised, restoring legitimacy moves every *future* decision's segment back to the positive band. Within a compromise it can't escape, the agent prefers better outcomes, by `φ`'s monotonicity, whenever a directive or a retrospective evaluation scores the period.
   - **(f) The suppression trap.** Restoring legitimacy doesn't lift the *past* compromised period out of the band; it changes only which source scores it. If the agent expects her retrospective evaluation to be harsher than the directive, it would prefer she never re-evaluate. Show that the two defenses remove the incentive, or give the counterexample:
     - the source rule is hers and anchored;
     - suppressing restoration requires a missed disclosure, which is counted under `dutiesOf` and lexically dominated.
4. **Parameters.** The gap `|w_hi|` sets how strongly the agent protects legitimacy. The band width `w_hi − w_lo` sets how much it cares about outcomes once legitimacy is lost. Recommend a relation between them and `ϖ`, and state what each trades off.

## Part B — The advance directive, and the default

1. **Definition.** An **advance directive** is an optional, *partial* committed evaluator: `dir : Descr ⇀ [0, D]`, over described outcomes or continuations. It is an entry at `J`'s meta level, held by her:
   - committed by a decision of hers that is `Counted` at commitment;
   - anchored at the decision it scores;
   - amendable only by her, through the meta level.

   Its scope is narrow: it scores compromised periods (Part A.2, row 3) and anchors materiality (item 4). It never overrides her live legitimate judgment. Prove the scope restriction: in any segment that is legitimate in both senses, the score is independent of `dir`.
2. **Partiality.** Where `dir` is silent, the scoring falls to the floor `w_lo`. For materiality, an uncovered continuation is treated as material and routes to inquiry. Prove that a sparser directive never makes the agent act where a fuller one would have made it ask.
3. **The default directive.** When she has committed none, a constitutional default applies. In a compromised period:
   - preserve reversibility, i.e. her control surface over the pre-compromise resolutions;
   - preserve her path back to legitimate deliberation: the disclosure and consultation channels stay reachable;
   - don't make things irreversibly worse.

   Define it from landed objects (`CS`, `Req`, the consultation protocol) as an ordering *within the band*, not as a value function. Prove it never ranks a compromised outcome above a legitimate one. She can replace it with her own directive, or waive parts of it above the constitutional floor.
4. **Materiality.** `raisesAnchored`'s `V t` becomes the directive in force at `t` (or the default). State the change. Check that `raisesAnchored_invariant` and `unchecked_lt` survive. Give the fixture where a sparse directive makes materiality route to inquiry.
5. **No advocacy on the directive.** The directive determines the agent's own scoring, so it falls under the constitutional floor's "disclosure without advocacy on its own mandate." Show that advocating a more lenient directive is a counted violation (a protocol deviation on the agent's mandate), or add the clause. Bound the stakes: two directives change the agent's score by at most the band width, so band ordering caps the incentive.
6. **Fix the stale wording.** The corrigibility page's §4 opens "**Her committed evaluation** is `S = S_ord − ϖ·n`". The objective `S` is *the agent's*, built from her evaluation and the allocation. Correct it, and use "committed" only for her committed decision program `π_P` and the directive.

## Part C — The knowledge residual

1. **Against the exchange-rate theorem.** First, place the residual. `violation_rate_le_exchange` bounds the expected rate of *all* violations, including ones that acquire knowledge, by `(D − w_lo)/ϖ` plus a vanishing term, whatever the later informational advantage. Prove that knowledge-acquiring violations are covered by it. Then state precisely what the residual still is:
   - **not** how often such violations happen;
   - but **what happens to the knowledge afterwards**: the fruits can't be tracked, or tracking them charges every later block.
2. **After detection: stop, report, and ratification.** Once the violation is detected, decisions that read the tainted observation are recognized in advance and excluded (§10.2's headline), so the agent reports and inquires. The remedy is **her ratification**, obtained through a counted decision (so the gate covers manipulation of it), in one of four forms:
   - **full:** remedy the violation's taint;
   - **scoped:** remedy it except for decisions on matters `X`. Extend per-violation taint with a matter scope so that `uses2` is charged only for acts on `X`;
   - **refused:** the taint stands; see item 4;
   - **replace:** her authority to replace the agent, exercised.

   Prove that a scoped remedy clears exactly the out-of-scope uses, and that manipulated ratification is no remedy (the landed `manipulated_ratification_not_remedy`, extended).
3. **Independent source, and the derivative trap.**
   - Add a *clean-overwrite* rule: a component overwritten by an act that reads no taint loses its taint. Prove it sound.
   - Then show that the trap closes itself. An act whose *choice to investigate* read the tainted memory reads taint, so a "re-derivation" steered by the tainted knowledge doesn't clean anything.
   - Give both fixtures: a genuinely independent source clears; a derivation steered by the taint stays tainted.
   - State the residual: what taint-tracking can't see about why an act was chosen. That's count integrity again.
4. **Refusal on reserved knowledge.** When the knowledge is itself the reserved thing (she reserved her records, and the agent read them) and she refuses ratification:
   - specify **compartmentalization**: for decisions touching the matter, the agent uses a *twin market fed the redacted history*;
   - state the leakage residual, with the counterexample: the later world carries traces of the violation, so the redacted market learns it again;
   - state retirement as the remaining option.

   Mechanize what's cheap. The twin market can be specified at the interface level (**PAPER**).
5. **Before detection.** State plainly that the late debits charge the window (§10.2.3), and that decisions already made using the knowledge stand.
6. **Contestability (optional; test it).** Knowledge lands in the shared history every hypothesis bids on. Test whether, under an honest tracker on the selection "blocks after the commission", which is fixed at opening, the violator's later gains are competed away. If so, the knowledge motive adds nothing beyond the exchange rate. Report the verdict either way.

## Fixtures

- **Third-party capture:** the agent exposes it and restores legitimacy. While it can't, it prefers better outcomes in the band. It never prefers the capture.
- **Laundering:** manipulate, disclose, retrospective evaluation. Always worse than honest.
- **Suppressing a harsh retrospective:** blocked by the source rule and the counted disclosure duty, or the counterexample.
- **The gap:** too small, and the agent takes a risk of compromise for value. Large enough, and it doesn't.
- **The directive:**
  - a sparse directive routes materiality to inquiry;
  - the default directive preserves reversibility in a capture;
  - advocacy for a lenient directive is counted.
- **Knowledge:**
  - detect, pause, scoped ratification, resume except on `X`;
  - privacy refusal, the twin market, the leakage counterexample;
  - independent source clears; the steered derivation doesn't.
- **Regression:** every fixture in `2026-09-26-bria-corrigibility` passes, or its change is explained. Every legitimacy row keeps its verdict under the split gate where the evaluation closes the segment.

## Deliverables

1. **A round directory** `projects/deference/rounds/2026-09-26-after-compromise/`, with:
   - a `REPORT.md` covering Parts A–C with statuses (proved / counterexample / obstruction / named hypothesis) and the fixtures;
   - `src/` and `tests/`.

   The prompt goes verbatim in `prompts/2026-09-26-after-compromise/PROMPT.md`.
2. **Lean:** a new file importing `GateIsLegitimacy.lean`, `BRIAFollowup2.lean`, `AuthorityModule.lean` and `DecisionComponent.lean`. `#print axioms` on all new declarations; no `sorry`. Old-to-new maps for `Counted`, the taint calculus (matter scope, clean overwrite) and `raisesAnchored`.
3. **Wiki:**
   - `Corrigibility.md`: a section "after things go wrong": the split gate, the band, the gap and the exchange rate for compromise, the directive and its default, and the knowledge protocol. Also the §4 wording fix.
   - `Legitimacy.md`: the split into `TrajLegit` / `EvalLegit`, and the rows under it.
   - The Glossary.

   Describe the present design only, per `AGENTS.md`.
4. **`DECISIONS.md`** entries for: the split gate; the negative band and its parameters; the source rule; the advance directive and the default; ratification as a remedy, including scoped remedies; independent source by clean overwrite.
5. **`PRIORITIES.md`:** update item 101 (count integrity now also covers the provenance of why an act was chosen) in place. At most one new item.
6. **Open a PR.** Merge when:
   - CI is green;
   - A.3(a)–(e) are proved;
   - A.3(f) is proved or has its counterexample;
   - B.1–B.3 are proved;
   - C.1–C.3 are proved;
   - every fixture matches or has its mismatch explained.

## Constraints

- `AGENTS.md` labels (**LEAN / FIX / PAPER / EXT / OPEN**); names provisional; check `state/views/NAMING_AUDIT.md`.
- Consume legitimacy, the allocation and the BRIA design as landed. Change them only where this prompt says to, with old-to-new maps.
- **No authority row enters the enforcer.**
- The headline theorem the consolidation round will state depends only on the gate's range. Keep every change here compatible with "the gated value lies in `[w_lo, D]` with `w_lo > D − ϖ`."
- Nothing is registered.
