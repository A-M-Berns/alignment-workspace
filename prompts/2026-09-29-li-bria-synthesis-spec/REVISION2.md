# Second revision dispatch — the final refinement pass (2026-09-29)

Relayed verbatim as sent by the maintainer in the same Claude Code session, after the
second pass had been pushed to PR #115.

---

Make one final refinement pass on PR #115 so that it is ready for maintainer review and merge.

**The deliverable is a clear, accurate specification of the research destination, with precise tests for recognizing success. It is not a construction or a promise that the requirements are jointly achievable.** We may have no clear strategy yet. Distinguish uncertainty about how to reach the destination from ambiguity about what the destination is.

Read the current branch and repository instructions. Independently check the mathematical objections below. Correct all affected documents, summaries, fixtures, and ledger entries consistently. Make any additional changes needed for accuracy and coherence, but avoid unrelated work or another expansive literature survey.

### 1. Encode the maintainer’s endpoint accurately

The maintainer’s position is:

> An absolutely ideal outcome would be updateless. A successful outcome may be updateful, provided it genuinely integrates logical beliefs and decision-making, behaves well on important decision problems, and makes substantive progress on the existing obstacles to logical-induction decision theory.

Accordingly, distinguish:

- **Supporting milestones:** LI and BRIA recovery results, computational existence, compatibility lemmas, and interface results.
- **Successful research endpoint:** a principled, computable LI/BRIA synthesis with substantive belief–decision integration, justified behavior on a specified benchmark class, and at least one meaningful advance on a recognized LI decision-theory obstruction. This endpoint may be updateful.
- **Ideal extension:** updateless or policy-level guarantees that address the additional failures of an updateful theory.

A supporting integration theorem can be publishable and valuable without, by itself, satisfying the full endpoint. Conversely, do not make updatelessness a requirement for calling the project successful.

Keep the specification neutral about architecture. A modular implementation can qualify. One market, one budget, auctions, published claims, blocks, and particular commitment mechanisms are not mandatory unless independently justified.

### 2. Fix the scope of BRIA recovery

The current unrestricted G3 and the updateless D4 target conflict in environments covered by P1′.

State recovery obligations with explicit domains:

- The full environment class on which a candidate’s general criterion applies.
- The restriction on which it recovers ordinary BRIA.
- Any continuation or block specialization.
- Any stronger policy-level extension and the recovery restrictions it requires.

For the updateful endpoint, broad action-level BRIA recovery may be appropriate. For the updateless extension, recovery may need to be limited to environments where the relevant local and policy-level demands are compatible.

Do not select a vague restriction such as “where updating is harmless” without defining it. If the appropriate maximal recovery domain is unresolved, record that precise specification question rather than quietly asserting a solution.

Retain P1′ as a useful boundary result, subject to checking its exact hypotheses. Present its conclusion only at the strength proved. In particular, a sufficient trackability assumption is not automatically a necessary condition, and one mugging result does not establish a universal obstruction for every cross-round commitment.

### 3. Make “no split-brainness” an actual acceptance obligation

The central ambition is that the agent’s logical assessments and the reasoning governing its choices form a jointly accountable process.

Do not assume that this must mean equality between every BRIA estimate and an LI expectation. The quantities may have different roles or information timing.

Specify what a candidate must exhibit:

- The semantic meaning and timing of each relevant forecast, estimate, or decision assessment.
- How logical information enters decision-making.
- How claims about decisions are held accountable when the agent controls which decisions occur.
- A formal interaction result excluding a stated failure mode or establishing a stated joint guarantee.
- An explanation of why this is more than an unrelated LI and BRIA placed beside one another.

Separate at least these achievements:

1. Market information improves decision performance.
2. Belief and decision assessments satisfy a compatibility relation.
3. Decision accountability prevents a specified self-confirming belief–action failure.

They are not interchangeable. If any can count as the integration component of success, explain its necessary strength and what it does not establish. Do not claim a performance improvement from compatibility alone.

Retain strong R4 as a possible formal target if defensible, but do not let it monopolize the meaning of integration. Give precise candidate tests where possible. Where a general definition remains unresolved, provide an explicit obligation for a future candidate to instantiate, rather than a slogan presented as a formal criterion.

### 4. Correct the remaining mathematical overclaims

**R4 derivability.** The current report says R4 is not derivable from LI and BRIA recovery. The review established gaps in the supplied proof, not a countermodel to the implication. Unless a valid countermodel is supplied, the correct status is:

> The previous derivation fails; whether the stated premises imply the strong compatibility property remains unresolved.

Distinguish an invalid proof, a false implication, and an unproved conjecture throughout.

Check the proposed repairs carefully. Making the chosen action public does not automatically make an arbitrary internal test set efficiently recognizable. Publicity also does not automatically justify applying a feedback theorem to pre-selection forecasts on a subsequently selected subsequence. State the required timing, access, generability, and feedback assumptions.

**Fixed testing schedules.** Retract or qualify “fixed test schedules are never BRIAs.” The off-schedule attacker promising one does not necessarily outpromise infinitely often. An environment where every option pays one and the agent always estimates one is an immediate warning against the unrestricted claim.

State the valid conditional obstruction, including the hypotheses that ensure infinitely many outpromises and absence of divergent negative test losses. Do not conclude that all valid testing must be adaptive unless that is proved.

**Computational lower bounds.** Not being an \(O(g)\)-computable agent does not imply that every instance, or a positive-density set of benchmark instances, exceeds the predictor’s runtime. Separate worst-case complexity, actual runtime on the benchmark sequence, and the predictor’s success frequency.

**Finite fixtures.** Audit every criterion-level conclusion for accidental reliance on a finite simulation or a few fixed bidders. Retain useful illustrations, but label their evidential role correctly. Add or amend only the focused checks needed for corrected claims.

### 5. Repair and tighten the advance diagnostics

The endpoint needs clear formal tests showing that a future candidate has made a substantive decision-theoretic advance.

**D1 / self-confirming pessimism.** The current assumption that no blind hypothesis promotes an identifiable option \(b\) conflicts with a class containing every efficient hypothesis: the constant bidder \((b,1)\) is already present. A bidder need not know its promise is correct to belong to the class.

Either formulate a genuinely different problem—such as identifying the relevant option being computationally difficult—with precise assumptions, or replace this diagnostic. Do not exclude the obvious promoting hypothesis without justification.

**D3 / Agent Simulates Predictor.** Remove the unsupported runtime inference described above. A bounded-simulation variant must be distinguished from the original proof-based problem, without asserting equivalence or preservation of the decisive obstruction merely because both involve a weaker predictor.

Do not use one-boxing frequency alone as the success condition when the predictor can default to two-boxing and leave the box empty. State the desired prediction–action behavior and payoff, together with assumptions under which that target is meaningful.

**T10 / information advantage.** Retain the fixture as an interface illustration. Audit the proposed theorem target independently: eventual settlement, pre-decision predictability, vanishing overall error, accuracy on endogenous test sets, and resistance to BRIA refutation are distinct properties. Do not move between them without proof. Any computational separation must give both sides comparable access and an explicit accounting of computation.

More generally, keep only a small number of well-posed advance diagnostics. Move incomplete candidates into a clearly marked provisional list rather than pretending they are ready acceptance tests.

### 6. Make the final test suite precise and usable

For each retained formal test, provide:

- An explicit environment or environment family.
- Observation, prediction, decision, and settlement timing.
- Predictor access and computational restrictions.
- The comparison class and information available to its members.
- The quantitative success condition.
- The mode and quantifiers of the guarantee: expectation, almost sure, asymptotic average, density, or finite-time.
- Whether success must follow for every satisfying agent or is claimed for a designated construction.
- A negative control or necessity witness where informative.
- Its role: recovery test, integration test, updateful advance test, or ideal updateless extension.
- Its status: established consequence, proposed acceptance target, or incomplete diagnostic.

State why the chosen success condition addresses the motivating difficulty. Do not treat a familiar problem name as a complete specification.

Explicitly mark whether a test supplies an external commitment contract, a new communication channel, or extra information. Such assumptions can support legitimate conditional results, but cannot silently count as progress on a problem lacking them.

Do not demand universal optimality against unrestricted code-sensitive environments. Define a justified benchmark class or leave the exact missing environmental assumption visible.

### 7. Produce a compact final statement of the destination

At the front of the main document, provide a concise acceptance statement a reader can use without reconstructing the history of the round:

> A candidate counts as a successful outcome if it establishes [precise core obligations], passes [named formal tests under their assumptions], and demonstrates [a substantive advance on an existing obstruction]. Updatelessness is an additional ideal target.

Make the logical structure explicit: which obligations are all required, which are alternative routes, and which are extensions. Do not leave this as an unresolved menu of desirable properties.

For any unavoidable open specification choice, say exactly what is missing and which acceptance judgment it prevents. We want maximal clarity, not false completeness.

Follow the concise statement with the detailed definitions, tests, boundaries, and prior-work comparison. Keep the continuation-BRIA specialization as one route. Remove duplication and obsolete claims; preserve revision history through commits rather than making the main specification read like a sequence of corrections.

### 8. Merge-readiness and stopping rule

Update existing documents rather than proliferating new ones. Check that the README, problem statement, suite, audit, report, PR description, and relevant ledger entries agree on:

- The updateful successful endpoint and ideal updateless extension.
- The domains of recovery.
- The actual status of P1′, R4, and the testing-schedule claim.
- What is proved, conjectured, merely illustrated, or still underspecified.
- What future evidence would justify declaring success.

Run the repository checks appropriate to the changes. Do not perform a deep construction search, extensive new formalization, or unrelated cleanup.

Finish with a short maintainer-facing report:

1. The final recommended acceptance standard.
2. The most discriminating formal tests.
3. The corrected or withdrawn claims.
4. Any genuinely blocking specification choices.
5. Verification performed and whether the PR is ready for review and merge.

Leave merging to the maintainer. The final product should accurately encode an ambitious research destination we can recognize when reached, even though we do not yet know how to get there.
