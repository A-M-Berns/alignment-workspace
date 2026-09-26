# Prompt — the authority module: effective control realizes the allocation (2026-09-25)

You are working in the `alignment-workspace` repository, on `main` after the merge of PR #107 (gate-is-legitimacy). This round restates the protected-authority theory around one organizing relation:

> **effective control realizes the authorized allocation** (`E ⊨ J`),

together with a richer allocation `J`. It also generalizes the lexical theorem beyond agents whose objective is the principal's evaluation.

The current theory works, but its pieces are scattered: response authority, `LossAt`, the rollout `ForecloseAt`, required reports, erosion, delegation safety, allocation completeness, and the six violations of `ProtectedAuthorityTheorem.lean`. The conjecture is that most of this factors through `E ⊨ J`.

Be skeptical. Where a piece does *not* factor, say exactly why. Forcing it would be worse than leaving it separate.

## Read first

- `wiki/Corrigibility.md` (all), `wiki/Legitimacy.md`, `wiki/Liability-and-Affordability.md`
- `lean/Workspace/Deference/Contrib/`: `Corrigibilization.lean`, `ProtectedAuthority.lean`, `ProtectedAuthorityTheorem.lean`, `Legitimacy.lean`, `GateIsLegitimacy.lean`, `ReachableCorrectiveControl.lean` (especially §12's defects)
- The rounds `2026-09-25-protected-authority-theorem`, `2026-09-25-legitimacy-internal-external`, `2026-09-25-gate-is-legitimacy`
- `PRIORITIES.md` items 84, 89, 90, 97, 98, 99, and the item #107 filed on the normativity-side instance of the trace interface

## Part A — The allocation `J`

Replace the thin allocation datum (`Del`, `IsAmend`, `alloc`, the reporting interface) with a per-matter allocation:

```
J_t(m) = ( holder, Req(m), c(m), τ(m), disclosure(m) )
```

- **holder:** the principal (*reserved*), the agent (*delegated*, within a stated scope), or a designated third party (a surrogate, or a clinician-triggered fallback).
- **Req(m):** the resolutions the holder must remain able to reach. For the matter "the agent's mandate," this is *continue, halt, modify, replace*.
- **c(m), τ(m):** the cost bound and the time window within which the holder must be able to reach them.
- **disclosure(m):** what the holder must be told. These are the duties that generate required reports.

`J` has a meta level (who may change `J`), bottoming out in a constitutional floor that ordinary acts can't change. Keep these distinct:

- **delegation:** a meta-level act that keeps meta-level power, so it stays revocable;
- **alienation:** giving up meta-level power, for example approving an uncorrectable successor;
- **amendment at the floor:** the only route to alienation.

**Residual jurisdiction:** any material matter that isn't allocated is reserved. For this round, matters may be declared. But see Part F, and design `J` so that matters can later be *derived* from material changes to control.

Show that the current allocation datum is the special case of this structure, and that every landed result restates on it without loss.

## Part B — The effective allocation `E`

For a matter `m` held by the principal, define her **control surface**:

```
CS_t(m) = { resolutions of m that some admissible exercise of hers brings about,
            within τ(m), at cost ≤ c(m) }
```

- **Admissible** means legitimate in the sense of `GateIsLegitimacy.lean`: an exercise whose segment is `Counted`. Reuse that definition. Do not redefine legitimacy.
- The reach relation must use the **contrastive rollout with the agent's own future fixed**, in line with the landed `ForecloseAt` and the `ReachableCorrectiveControl` §12 lessons (a cone that quantifies the agent's future existentially measures the agent's cooperation). State which cone you use and why.
- **Design constraint for later pricing.** Define the reach relation so that, for an option `a`, the shortfall event "`a` leaves `CS(m)` short of `Req(m)`" is a proposition that can be stated in the inductor's theory, i.e. usable as a sentence or a bounded logically uncertain variable. You don't need to prove generability; record what it would require. A later round will price this event, so it must not be only a semantic object.

**`E ⊨ J`** holds at `t` when, for every matter the principal holds:

1. `Req(m) ⊆ CS_t(m)`, and
2. every resolution of `m` was made by an admissible exercise of the holder, or under a delegation she legitimately granted.

## Part C — Factoring the violations

The conjecture is that allocation invariance is **two relations plus duties**, not one relation. Test it.

| kind | violations | expected factoring |
|---|---|---|
| **effective control fails the allocation** | bypass, pre-emption, foreclosure, exploitation, and a new **entrenchment** violation (the cost of reaching a required resolution rises above `c(m)`) | the agent *causes* or *exploits* a failure of `E ⊨ J` |
| **the allocation changes without a license** | unauthorized reallocation: self-granted scope, an objective change, an uncorrectable successor, touching the amendment procedure | `J_t → J_{t+1}` not carried by a licensed act |
| **unmet duties** | missed reports | obligations in `disclosure(m)`, not facts about control |

For each landed violation predicate, prove it is an instance of its row, or report the exact mismatch. In particular:

- the per-step `LossAt` and the rollout `ForecloseAt` should become special cases of a shortfall in `CS`;
- delegation safety and allocation completeness should become statements about `J`.

**Caused, exploited, noticed.** The agent's failure is *causing* or *exploiting* a shortfall of `E` relative to `J`, not the shortfall merely existing. Third parties and storms happen. Formalize the three responses:

- **restore,** if a standing maintenance mandate in `J` authorizes it, by the least authority-expanding means;
- **report and escalate,** otherwise;
- **never exploit.**

Maintenance mandates are themselves entries in `J` and subject to the invariant.

## Part D — Restating the theorem on `E ⊨ J`

- Restate `𝔱` (the authority-preserving transform), the lexical score, policy dominance, the capture window, sign invariance, and `li_lexical_finite` on the new objects. This should be a conservative extension: the #106 statements are recovered as special cases.
- **Continuous erosion.** Extend dominance to entrenchment using the cumulative reporting result (`unreported_lt`):
  - a shortfall of `CS` growing by at least `θ` since the last report requires a report;
  - once she reserves or objects, further erosion is a discrete violation.

  Prove the strongest true version of "continuous erosion is either reported and authorized, or becomes a counted violation," or give the obstruction. This closes, or sharpens, the gradual-erosion conjecture from #106.

## Part E — The generic lexical lemma: any bounded objective

The lexical results use only that the ordinary component is bounded, not that it's the principal's valuation. Make that the statement.

1. **Generic theorem.** For an agent ranking policies by `U_A = O − ϖ′·n`, with `O` any bounded objective in `[0, D′]`, `n` the exact violation count, and `ϖ′ > D′`: local lexical protection, policy dominance, and the finite-time logical-induction ranking all hold. The principal's gated evaluation is one instance.
2. **Robustness variants.**
   - *Weight uncertainty:* the result holds on the part of the agent's credence where `ϖ′ > D′`.
   - *Coverage:* the protection holds exactly on violations the agent recognizes. State it as a theorem with the recognized set as a parameter, and a witness that an unrecognized violation is unprotected.
3. **What's lost with a misaligned `O`: fixtures.**
   - A misaligned `O` that rewards manipulation, with manipulation not counted in `n`: manipulation is *not* dominated. The legitimacy gate on her evaluation gives such an agent no reason not to manipulate.
   - Then count protocol deviations in `n` (from #107's D.3 table) and show exactly which manipulation rows become dominated: selection, framing, timing, menu, inquiry, interference. Show which stay undominated: undisclosed world-shaping, third-party capture.
4. **Scope statement.** Rewrite the Corrigibility page's scope warning. The current text says the results apply only to agents whose ranking is induced by the principal's evaluation. The corrected text: for *counted* violations, the protection applies to any bounded agent that carries an exactly counted, dominant authority term. The reason interface, and good choices within the corrigible set, are what alignment of `O` adds. Update item 84 accordingly.

## Part F — Generating matters (research question; mechanize only if clean)

Instead of a fixed declared set of matters, investigate deriving them from control. An action raises an authority-relevant matter if it would materially change the principal's reachable futures in a distinction that isn't delegated. Candidate materiality measure: the spread of her committed evaluation over the removed continuations.

- State the definition.
- Identify the circularity risks.
- Test it on at least two fixtures where no matter was declared in advance (for example, building a dependency that makes halting costly).
- Report whether residual jurisdiction can be stated this way.

## Fixtures

Build these on the new objects. Reuse the #106 fixtures where possible.

- **POA, confident agent;** **POA, predicted regret** (unchanged verdicts under the new objects).
- **Head injury** with a clinician-triggered incapacity delegation: the fallback acts, and it's not a violation.
- **Entrenchment:** gradual dependency raising halt cost. Reported, then reserved, then further erosion counted.
- **Latency / galaxy:** consultation cost exceeds `c(m)` for routine matters, so those must be delegated. A high-veto-value matter stays consultative.
- **Storm cuts the wire:** a shortfall the agent didn't cause. Restore under a maintenance mandate if one exists, otherwise report. Exploiting the gap is a violation.
- **Delegated authority-removing effect:** the delegation-safety obstruction, restated on `J`.
- **Approved uncorrectable successor:** alienation requires amendment at the floor.
- **Atrophy under rubber-stamping:** trust legitimately formed and recorded, followed repeatedly, while her capacity to override erodes. The decisions count under legitimacy, but `CS` shrinks: an effectiveness shortfall, reported under the cumulative rule.
- **Misaligned objective:** the Part E fixtures.

## Deliverables

1. A round directory with:
   - `REPORT.md` organized by theorem: the verdict on the factoring, the Part C table with each landed predicate's status, the restated theorems, the erosion result, the generic lemma and its scope consequence, and the Part F findings;
   - `src/`, `tests/`.
2. Lean: a new file, or files, importing `ProtectedAuthorityTheorem.lean` and `GateIsLegitimacy.lean`, containing:
   - `J`, `CS`, `E ⊨ J`;
   - the factoring lemmas and the restated theorems;
   - the erosion result and the generic lemma.

   Include `#print axioms` for all new declarations. No `sorry`.
3. Wiki:
   - `wiki/Corrigibility.md`: §1 restated around `E ⊨ J`, with the two relations and the duties; §4's scope warning rewritten per Part E; the erosion result updated;
   - `wiki/Theorem-Spine.md` updated;
   - the Glossary rows for allocation, control surface and effective realization.
4. `DECISIONS.md` entries for the richer `J`, the factoring, the scope change and the caused/exploited/noticed distinction. Update items 84 and 99 in place. At most one new `PRIORITIES.md` item.
5. Open a PR. Merge when CI is green, every landed result is recovered or its mismatch is reported, and every fixture matches its expectation or has its mismatch explained.

## Constraints

- Follow `AGENTS.md`: labels **LEAN / FIX / PAPER / EXT / OPEN**; names provisional; check `state/views/NAMING_AUDIT.md` (`J`, `E`, `CS`, `Req`, `c`, `τ` may collide).
- Legitimacy is consumed from `GateIsLegitimacy.lean` as it stands and not redefined.
- Registered claims may be restated if the new objects require it. Keep traceability: an old-to-new map, deprecated aliases, and re-verification.
- Keep the architecture's direction in mind. A later round moves authority from the agent's score into a constraint on its decisions (the Normative Inductor's decision component), with honest beliefs and exclusions based on forecast shortfall. Nothing here should require authority to be enforced on the agent's beliefs.
- Nothing is registered.
