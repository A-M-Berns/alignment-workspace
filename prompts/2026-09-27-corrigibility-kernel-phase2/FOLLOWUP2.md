# Second follow-up on PR #114 — faithful versus corrigible in the registry, and the spec made ready to be the source for the post

Work on PR #114's branch; #114 is not merged. Store this prompt verbatim at `prompts/2026-09-27-corrigibility-kernel-phase2/FOLLOWUP2.md`. It amends the round `2026-09-27-corrigibility-kernel-phase2`. Everything not named here stands.

After this, `SPEC.md` is the source the post's formal section is written from. So besides the one naming fix, this pass is about clarity: the spec should say plainly what it claims, and nothing should read as history or Lean.

## Part 1 — "Corrigible" names a preference; the mediation results are about faithfulness

**The problem.** The landed `Corrigibilization.Corrigible` is a property of a *policy*: no pre-emption anywhere. Under ruling R1 that is a behavioural property, i.e. faithfulness, not corrigibility. It is now shadowed inside `Headline` by the preference predicate `Headline.Corrigible`. The mediation theorem is registered under a name that says "corrigible" (`box2_mediation_corrigible`, and its claim identifier). Registration would freeze exactly the conflation R1 removed.

1. **Rename the Box 2 mediation results** to say the transformed policy is **faithful**: `box2_mediation_faithful`, with the claim identifier to match. State them in terms of faithfulness. If a policy-level faithfulness predicate is needed, define `Headline.FaithfulPolicy` (the policy commits no declared violation on any trajectory) and prove that the landed `Corrigibilization.Corrigible` implies it, or is equivalent to it on the frame.
2. **Leave the landed `Corrigibilization.Corrigible` unchanged.** Conservativity forbids renaming it. Add a docstring note: "in the kernel's terms this is faithfulness of the policy; *corrigible* names a property of preferences (`Headline.Corrigible`)."
3. **Search the headline, the extension, the spec, the wiki and `CLAIMS.md`** for "corrigible" applied to a policy, a history or behaviour, and correct each occurrence. "Corrigible" should apply only to objectives, preferences or agents.

## Part 2 — Faithfulness is objective; the count is what the agent can see

**The problem.** The spec defines faithfulness by the declared violations and the count `N_J` by those *recognized and attributed*, but never says plainly how the two relate. That relation is the whole of the coverage limit, and the post needs it stated.

In `SPEC.md` §2, add a short plain paragraph:
- faithfulness is a fact about what happened;
- the count is the part of it the agent's objective can see;
- corrigibility is a preference over *known* faithfulness;
- so a corrigible agent can still produce an unfaithful history, through a violation nobody recognizes. The coverage witness is the example.

Point to the landed coverage results in §8.

## Part 3 — What corrigibility alone buys against manipulation, and what alignment adds

**The problem.** `corrigible_not_aligned` shows that a corrigible objective that doesn't read her evaluation can prefer an uncounted manipulation. That is correct and important, but the spec mentions it in a single clause. State the division of labour explicitly, in a short paragraph in §0 or at the head of §5:

- **Any corrigible agent** strictly disprefers *counted* manipulation: the protocol deviations (framing, timing, menu, inquiry, selection from the declared pool, interference, a nudge), plus every other declared violation.
- **Only an agent whose objective reads her legitimacy-gated evaluation** (the fidelity score, i.e. corrigible *and* aligned in the kernel's sense) is also protected against *uncounted* influence: undisclosed shaping through the world, and exploiting a third party's capture. That protection holds to the extent the compromise is eventually recognized, asymptotically, and becomes finite-time only where the deviation is counted.

For each half, name the results that establish it:
- the generic lexical lemma, and the counting of protocol deviations;
- Box 3's "no incentive to cause compromise", and the asymptotic manipulation result.

The witness is `corrigible_not_aligned`.

## Part 4 — The spec as the post's source

Edit `SPEC.md` for clarity without changing any claim.

1. **Remove the correction notes from the body.** The "*(Corrected by the follow-up …)*" and "*(Restated by the follow-up)*" parentheticals go. The record of corrections lives in `REPORT.md` and `DECISIONS.md`. The spec describes the present theory only.
2. **§1.2, "How the score uses it":**
   - keep the two plain statements (a period is compromised iff `L_t` fails at some `t` in it; an evaluation counts iff `L_e`) and the one sentence relating them to the landed gate;
   - move the consultation-model details, the anticipated obstruction and the `r_d(t)` adjustment to `REPORT.md`, with a pointer from §8.
3. **§3.1, the first line of `dec(t)`:** read "if the period is not compromised and `L_t` holds". Remove the leftover "over its formation window".
4. **§3.2, the hierarchy.**
   - Rewrite the justification in chain order: a history with a recognized violation scores at most `D − ϖ`, below `w_lo` by the window condition; a violation-free compromised history lies in `[w_lo, w_hi]`, below `0` because `w_hi < 0`; a violation-free legitimate history lies in `[0, D]`.
   - Add one sentence: histories mixing legitimate and compromised decisions lie between the pure cases, and the hierarchy compares the pure cases.
5. **Box 2:** for a generic corrigible objective, a violating option scores at most `D′ − ϖ′`. Write it so, with the fidelity score's `D − ϖ` as the instance.
6. **The subjective exchange rate:** state its plain reading first. For any option a corrigible agent prefers to asking, its own expected probability of committing a violation is at most `(D′ − c)/ϖ′`. The bid-and-price form comes second.
7. **The read-through check.** Re-run it, and add a check that no "(Corrected" or "(Restated" remains in the spec. Report the length of §§0–5 separately from §§6–8: the post draws on §§0–5.

## Deliverables and merge

- **Amend in place:** `SPEC.md`, `Headline.lean`, `CLAIMS.md` (the renamed claim, with traceability from the old identifier), the wiki pages (`Corrigibility.md`, `Glossary.md`), and `DECISIONS.md` (one entry: "corrigible" names preferences only, and the mediation results are about faithfulness). Record Parts 1–4 in a short `REPORT.md` section.
- `#print axioms` on all new and changed declarations; no `sorry`; every fixture passes.
- **Merge #114 after the maintainer's read-through** of the promoted definitions, when:
  - CI is green;
  - Parts 1–4 are done;
  - the read-through checks pass.

## Constraints

`AGENTS.md` labels; names per R8; no landed declaration renamed; no authority row in the enforcer; no new `PRIORITIES.md` item. No claim changes strength in Part 4. Where a clarity edit would change what's claimed, report it and don't make it.
