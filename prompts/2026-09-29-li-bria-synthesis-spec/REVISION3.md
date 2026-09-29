# Third revision dispatch — the final amendment (2026-09-29)

Relayed verbatim as sent by the maintainer in the same Claude Code session, after the
third pass had been pushed to PR #115.

---

Make a small, final amendment to PR #115 before maintainer review and merge. Preserve the current structure and corrected mathematics. This is not another broad research round or construction search.

The specification now largely captures the intended destination: **a principled LI/BRIA synthesis that may be updateful, with genuine belief–decision integration and a substantive advance on an important LI decision-theory obstruction; updatelessness is the ideal extension.**

Address the following remaining issues consistently across the problem statement, suite, report, README, audit, PR description, and relevant ledger entries.

### 1. Do not make A1 the mandatory definition of success

The acceptance statement currently requires I3 specifically on A1, the belief-disagreement troll, and calls A1 the sole well-posed advance diagnostic.

That is too restrictive and overstates A1’s maturity. The maintainer’s endpoint requires substantive integration and progress on an important obstruction, not necessarily success on this particular constructed environment.

Revise the acceptance statement so that:

- The supporting milestones and integration obligations remain substantive.
- A candidate must prove that its integrated process addresses a precisely specified failure mode or recognized obstruction.
- A1 is one proposed diagnostic, not the unique mandatory route.
- A replacement diagnostic must meet an explicit qualification standard: complete semantics, quantified success condition, justified relationship to an existing obstruction, matched assumptions, and an explanation of what existing guarantees fail to establish.
- One theorem may discharge both an integration obligation and the substantive-advance obligation if it genuinely establishes both.

Do not dilute this into “any improvement counts.” Preserve the distinction between a useful information-transfer theorem and a decision-theoretic advance.

### 2. Correct A1’s status and identify its missing semantics

A1’s troll reads pre-selection forecasts \(F_k(c)\). Section 5 says the score of an unselected option lacks settlement. Before A1 can be a complete formal acceptance test, specify what those forecasts are:

- Conditional expectations of specified variables?
- Prices of explicitly defined contracts?
- Selectively evaluated forecasts?
- Additional reports outside the LI market?

These are alternatives to distinguish, not interchangeable descriptions.

A1 also claims that two fixed points satisfy M1–M4. An intuitively self-consistent forecast–action pair is not yet a witness satisfying the full LI and BRIA requirements. Either justify that claim at its stated strength or downgrade it to a proposed failure configuration whose compatibility with the milestones remains to be checked.

Explicitly identify the possibility that a favorable report changes the environment and makes crossing successful. A future solution must explain whether it overcomes the intended epistemic obstacle or establishes a different report–action coordination result.

Do not solve A1 in this pass. If its semantics cannot be completed with a small clarification, mark it **provisional**, list the exact missing definitions and proof obligations, and remove claims that it is already fully well-posed or demonstrably equivalent to an established Troll Bridge obstruction.

Distinguish the precision of a success condition from whether anyone knows how to achieve it. An unproved target can be a valid test; an undefined target cannot.

### 3. Fix T10’s negative control

The current statement that later deductive settlement means “the market has no advantage” and “both sides are at chance” is unsupported.

A market may predict a sentence before its deductive settlement using other patterns or arguments. Replace the claim with the justified conclusion:

> The stated pre-decision deduction argument no longer guarantees an advantage.

If retaining a chance-performance control, supply an explicit unpredictability assumption and explain why it yields that conclusion. Otherwise omit it.

### 4. Resolve active LI versus passive-only recovery

The endpoint requires LI on the active trajectory, but the checklist still permits passive-only LI as a fallback.

Make the distinction consistent:

- **Active LI** is required for the endpoint’s advertised guarantee about the agent’s beliefs during decision-making.
- **Passive-only LI** is a weaker supporting milestone, not an alternative that automatically satisfies that endpoint.

If proposing a different endpoint based on passive recovery, state and justify its weaker achievement separately. Do not silently treat it as equivalent.

### 5. Final consistency check and stopping point

Make any additional small corrections directly necessary for these amendments. Avoid new architecture, new benchmark families, extensive literature work, or unrelated refactoring.

Check that the final documents agree on:

- Updateful success versus the ideal updateless extension.
- Required milestones versus weaker supporting results.
- The standard for a substantive integration result and decision-theoretic advance.
- Which tests are fully specified targets and which remain provisional.
- What a future candidate must prove before being declared successful.

Run checks appropriate to the edits. Finish with a concise report of the changes, remaining provisional items, and merge readiness.

The goal is a mergeable research specification, not a completed theory. Leave merging to the maintainer.
