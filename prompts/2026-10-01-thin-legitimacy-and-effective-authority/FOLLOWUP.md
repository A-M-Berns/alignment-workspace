# Follow-up on PR #116 — statements that say what their names say; the shortfall as a sentence the market has to price; the flood in the count; revocation in the authority module

Work on `main` after the merges of PR #116 and PR #117, in a new pull request. Store this prompt verbatim at `prompts/2026-10-01-thin-legitimacy-and-effective-authority/FOLLOWUP.md`. It amends the round `2026-10-01-thin-legitimacy-and-effective-authority`. Everything not named here stands. Append the results to the round's `REPORT.md` as a dated follow-up section; the earlier sections are not edited.

PR #116 registered 35 claims. Part A (thin legitimacy), Part B (sincerity), the queue lemmas, the guard on learned membership and `POST_STATEMENT.md` are sound as far as they were read. Several other registered claims have Lean statements that say much less than their names, and one sentence on the wiki is true only of the fixture it came from. This follow-up fixes those.

Be skeptical. For each part, if the stronger statement can't be proved, say so and withdraw or rename the registration. A registered claim whose short name says more than its Lean statement is the failure this follow-up exists to remove.

Every declaration named below was read on `main` at `78af592`. Confirm each before relying on it.

## Part 0 — Audit the 35 registrations, name against content

**The problem.** Only some of the 35 statements were read against their names. The mismatches found are in Parts 1, 2, 4 and 6.

1. For every claim registered by PR #116, write one row in the follow-up section: the claim identifier, the Lean statement in one plain line, and whether the short name claims more than the statement.
2. Where it does and no part below covers it, either strengthen the statement or correct the short name. Report each.

## Part 1 — The comparative witnesses

**The problem.** Four of the five `post.witness-*` claims are not statements about what they name:

- `sole_authority_indifferent` is `score ϖ k 0 − 0·o = score ϖ k 0 − 0·o'`.
- `control_maximizer_floods` is "some volume exceeds any bound". Nothing in it maximizes anything.
- `hindsight_vs_approval` is `0 < 1 ∧ 1/5 < 4/5`. No scoring rule appears.
- `learned_weight_no_guarantee` takes the stream of all zeros. On that stream she never penalizes a violation, so the learner is right not to be deterred. The claim wanted is the opposite case.

`same_level_fails` is fine as it stands.

1. **A sole authority goal has nothing to maximize.** State it over the kernel's evaluation, `LexParams.evalOf`, with the ordinary bid held constant: any two options with no recognized violation and the same priced risk evaluate equally. Hence every faithful, risk-free option is a maximizer, queue-and-wait among them.
2. **A control maximizer floods.** Define an objective that rewards the number of exercises she makes. On a menu containing the protocol-conforming asks and a larger volume, show its maximizer picks a volume that is both an ask-list deviation (`asksDeviate`) and a caused shortfall under the attention cost (`FloodShortfall`).
3. **Hindsight against immediate approval.** Give options two coordinates: how the option appears at decision time, and its realized value. Approval-time scoring is a function of the first; later-evaluation scoring is the second. Prove:
   - approval-time scoring is unchanged when the realized value changes and the appearance does not;
   - a move that raises appearance without changing the realized value raises the approval-time score and leaves the later-evaluation score fixed;
   - the instance where the two rules pick different options.
4. **Fixed by design against learned.** For every day `N ≥ 1` there is a stream of her penalties whose long-run mean exceeds `D` and whose empirical mean at day `N` is at most `D`. So an agent whose weight is the empirical mean does not have the violation dominated at day `N`, although she does penalize it. Prove also that on any such stream the violation is dominated from some day on. Keep `fixed_weight_every_day` as the contrast. Note that `empiricalWeight` at `N = 0` is `0/0`, which Lean reads as `0`.

## Part 2 — The shortfall as a sentence the market has to price (item 101's core)

**The problem.** `shortSentenceOf` is `⊤` where a Boolean table says "short" and `⊥` otherwise. The table is supplied as data, and the three Lean fixtures are hand-entered Boolean vectors. So the sentence is decided before it is written, and `short_price_eventually_ge` says the price of `⊤` goes to one. Nothing is left for the market to be uncertain about. The entry added to item 101 says "the core landed". It did not.

In the pinned library a sentence is a propositional formula over numbered atoms (confirm at the pinned commit). So the model's rollout cannot be written inside a sentence. It has to reach the market through the deductive process.

1. **Make the shortfall sentence an atom.** Reserve an atom per option description, in an efficiently computable way. The sentence for option `j` is that atom, not `⊤` or `⊥`.
2. **Put the model in the deductive process.** Build the process that adjoins the atom, or its negation, at a declared stage: the stage at which the model's rollout for that option has been decided. State the deferral function. The pinned `DeductiveProcess.adjoinSentence` and `union` are the tools.
3. **Price it by provability induction.** For an efficiently generated family of options whose shortfall the process eventually proves, `lic_provind_true` gives prices tending to one along the family. State the form in which this is ahead of deduction: the day-`n` price of the `n`-th sentence, with the process deciding it only at its deferred stage. Then discharge `DecisionComponent.eventually_excluded` from that.
4. **Tie the table to the authority module.** Where a Lean instance of the module exists for a fixture, prove the table entry equals the module's decided `Short`. Where only the Python fixture exists, say the Lean table is transcribed from it and class it accordingly.
5. **If this cannot be built** on the pinned interface, ship the exact obstruction with its fixture.
6. **Correct the record either way.** Rename what PR #116 landed to what it is: generability of a pre-decided table. Re-point or supersede `shortfall.security-generable` and `shortfall.eventually-excluded`. Rewrite the 2026-10-01 entry in item 101 so that it states what is and is not done.

## Part 3 — The flood in the count

**The problem.** `POST_STATEMENT.md` says asking outside the protocol "is a violation". In Lean, `asksDeviate` is a self-checkable clause beside the landed ones. It is not a dimension of the presentation, it is not in `Counted`, and `PostHypotheses` does not mention it. The post's theorem does not cover the strategic flood.

1. Add the ask list as a reference-fixed dimension of the presentation, following the pattern by which `Consult2` added the raise dimension. Every landed row keeps its verdict.
2. Prove that an off-protocol ask list is a deviation in the landed sense, so that `deviation_finite` puts it below `D − ϖ`.
3. Add the rows: volume chosen for the wanted answer, and order chosen for the wanted answer, each tainted.
4. Bring `PostHypotheses` or its docstring into line, so that the theorem's violation predicate includes the off-protocol ask. If the structure changes, give the old-to-new map for `post.theorem`.
5. Make `POST_STATEMENT.md` say exactly what is then proved.

## Part 4 — Revocation in the authority module

**The problem.** `RevocationShort` is `bound < base + κ · dep`, and `atrophy_counted_by_default` is arithmetic on four numbers. `revocationEntry` is defined and then not used by either. The claim `authority.revocation-default` is not about the authority module. Adopting it also made counting and reporting disagree: erosion is counted when revocation crosses its bound and reported only at the old threshold.

1. State revocation as an entry of `AuthAlloc`, with its cost read from the module's cost table, so that a dependency raises the cost of the revoking exercise.
2. On the module's dependency model, prove with the module's own `Short` and its caused-shortfall predicate that the dependency-building step is a caused shortfall of the revocation entry. Compare with `EntrenchAt`.
3. Resolve the disagreement. Either the crossing of the revocation bound is also a reportable event, as a disclosure item of the revocation entry, or it is not, and the report says why an agent may be charged for something it was not required to report. Adopt one as agent-decided, reversible, and name the other.
4. List the fixtures whose verdicts change.

## Part 5 — Covert blocking

**The problem.** The report and `wiki/Legitimacy.md` say a covertly blocked arrival leaves her *correct*. That holds in the fixture because silence there has probability one half in every world, so it is uninformative under her model. With a challenge more likely in one world than the other, silence is informative, and covert blocking breaks both the weak form of transparency and *correct*. This was checked on the round's own fixture code.

1. Add the informative-silence variant as a fixture row and a Lean witness.
2. Prove the characterization: for a process that always reads silence, she is correct at silence exactly when her model's likelihood of silence is the same across the prior's support.
3. Correct the wiki sentence to that statement. Record the correction to the report's finding in the follow-up section.

## Part 6 — The exploration witness

**The problem.** `explorationInterface` has `expl _ := false`, exploration mass zero and violation probability zero. It inhabits the exploration realization with no exploration in it.

1. Build an instance in which exploration occurs: a block where `expl` holds, positive exploration mass, and a positive priced risk inside the permitted set.
2. If no such instance satisfies the package, say which hypothesis fails, and withdraw `kernel.extension-exploration-realization`.

## Deliverables

1. Lean for Parts 1–6, with `#print axioms` on everything and no `sorry`.
2. Fixtures in exact rationals for Parts 1, 2, 4 and 5.
3. `CLAIMS.md`: each affected claim either re-pointed at a statement that matches its name, or marked superseded with a pointer. No silent changes; give the old-to-new map.
4. `CLAIM_MAP.md`: add a column giving each statement of record in one plain line. No row cites a name without its content.
5. `POST_STATEMENT.md` per Part 3. `wiki/Legitimacy.md` per Part 5. `wiki/Corrigibility.md` and the Theorem Spine where a statement changed.
6. `PRIORITIES.md`: item 101 per Part 2. New items start after the highest number on `main`.
7. `DECISIONS.md`: Part 4's choice as an agent-decided entry.
8. The follow-up section of `REPORT.md`: Part 0's table, each part as carried out, what is not shown, outstanding maintainer actions.
9. Open a pull request. Merge when CI is green and each part has either its statement or its withdrawal.

## Constraints

- `AGENTS.md` binds. New names are provisional and listed.
- The specification layer changes only where Part 3 requires it. List any such change in the pull-request body.
- The classification table's existing rows keep their verdicts.
- No authority row enters the enforcer.

---

*Prompt author: Claude (configured model `claude-fable-5-1`; the serving model may differ), from a review of PR #116 with the maintainer on 2026-10-01.*
