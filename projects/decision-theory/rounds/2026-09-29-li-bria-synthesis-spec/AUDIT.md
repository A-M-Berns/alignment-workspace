# Audit: prior approaches, compatibility of the requirements, open specification choices

Labels as in `PROBLEM_STATEMENT.md`; M1–M6, I1–I3, A1–A2 are its §2, §3, §7.
Citations were checked against the sources on 2026-09-29 by fetching them; where a
remembered attribution did not check out, that is said.

## 1. Prior approaches: what each guarantees

| approach | guarantee, with quantifiers | assumptions | limitations, by status | requirements met | what would be an advance |
|---|---|---|---|---|---|
| **Logical induction** — Garrabrant, Benson-Tilsen, Critch, Soares, Taylor 2016, arXiv:1609.03543 | No e.c. trader exploits the market (Def. 3.0.1); convergence, calibration and unbiasedness on e.c. subsequences, conditionals, expectations of bounded variables, self-trust (§4), all asymptotic | computable `D̄`; polynomial-time traders; purely epistemic | *proved*: nothing about actions; unbiasedness only on weightings a trader can compute at forecast time; forecasts of variables that never settle are unconstrained; *stated by the authors*: no rates | M1 (epistemic), M2, M6(ii) | any action guarantee that consumes the market's expectations without conditioning on untaken actions |
| **LIDT with ε-exploration** — the procedure Garrabrant 2017 ("Two Major Obstacles for Logical Inductor Decision Theory") and Demski and Garrabrant 2018 (*Embedded Agency*) describe | none stated; the posts are obstacles: (1) bets conditional on the untaken action never settle, and with exploration a predictor as capable as the agent separates explored from deliberate actions; (2) no updatelessness for computations | LI prices; a fixed exploration rate | *illustrated*: 5-and-10 with a capable predictor; counterfactual mugging with a logical coin; *conjectured*: nothing positive | none of M3–M5; identifies M4, A1's failure shape and A2's obstruction | a testing rule under which a test is a choice (M4), which BRIA supplies; obstacle (1) survives as untested optimism in the compatibility derivation (§5 of the problem statement) and as A1 |
| **Asymptotic decision theory** — gallabytes 2016 (blog and IAFF; the PDF carries no author line, and the post credits Taylor, Eisenstat and Benson-Tilsen for the ideas — a remembered attribution to other authors did not check out), improved writeup Diffractor 2018 | Thm 2 (2016): soft-argmax over a *finite* list of agents asymptotically dominates the list on a continuous ("fair") embedder, under convergence of the relevant expectations; the 2018 writeup finds the optimality proof flawed and restates it as **Conjecture 1** under "regret-free" environments | finite agent list; continuous embedders; convergent limits | *illustrated*: ASP one-boxes, Newcomb one-boxes, chicken reaches a mixed equilibrium; counterfactual mugging does not pay; *proved*: only fairness of continuous embedders; the 2016 PDF flags its own proof as "a bit suspect" | M1 (limit-computable, given LI); M3 only conjecturally and for finite lists | a proved dominance statement over an infinite e.c. class — M3's coverage over `H^P` — with the comparator the claim rather than the embedder's counterfactual |
| **Troll Bridge** — Demski 2019, results due to Eisenstat; *Passing Troll Bridge*, Diffractor 2018 | negative: proof-based DT with the chicken rule, and the probabilistic variant with a `P(cross)=0` clause, refuse to cross by a Löbian proof; Diffractor's budget-filtered LI crosses "with arbitrarily high probability" as a stated **conjecture** | the troll reads the *reason* (the consistency of the theory; the clause that fired; the exploration flag) | *proved*: the Löbian refusal; *conjectured*: the budget-filtered fix; *unknown*: exploration driven by a source the troll cannot see | none; the family diagnoses M4 and gives A1 its shape | T3: (b), (f) at criterion level with the troll's access changed and said so; (c), (d) construction-dependent; (e) = A1, the proposed advance; (a) stays in register (iii) |
| **BRIA** — Oesterheld, Demski, Conitzer, TARK 2023, EPTCS 379 pp. 421–440, arXiv:2307.05068 | Def. 7: no overestimation and coverage of every e.c. hypothesis; Thm 1: a BRIA covering a c.e. class of `O(g)`-computable hypotheses is `O(g q)`-computable (first-price auction), for every reward sequence; Thm 2: not `O(g)`-computable (worst case); Thm 3: an efficiently identifiable option with an e.c. lower bound is matched on average; Thm 4: boundedly vMWC-random rewards with e.c. means are attained; Thm 5: folk theorem, with randomization; App. C: Hannan consistency unachievable and undesirable; App. D: estimates are necessary against biased testing | finite menus; rewards of the chosen option only; `DP_t` may depend on past choices; myopic target | *stated by the authors*: myopia; counterfactual rewards undefined; limit statements only; no coherence à la LI (open question); no policy-level result; ignores the ability to randomize; *derived here* (`PROBLEM_STATEMENT.md` §4): global no-overestimation alone permits cross-subsidy and coverage of an e.c. tracker removes it where the subsidizing reward is trackable (P1′); the conditional fixed-schedule obstruction; the first-price auction is trapped by the tentative troll while Thm 1 holds | M1, M3, M4 at unit granularity; M5 via the continuation form in this repository | M2(c) with the class `H^P` and the integration results I1, I3 — the coupling the paper's §8 conjectures ("Garrabrant inductors with (pseudo-)randomization could be used to construct BRIAs") |
| **Continuation BRIA** — `wiki/Continuation-BRIA.md`; round `projects/deference/rounds/2026-09-08-continuation-bria/` | the weighted criterion; existence iff non-dominance of the system schedule; continuation competence under (BR); `Regret = SHIFT + SLACK + LEARN` exact; regret against all legitimate policies false | system-scheduled horizons; realized gated execution; opening-timed subsidy; published claims; an external execution contract | *derived on Lean algebra*, unregistered; `SHIFT`/`SLACK` certificates open (item 86); the LI coupling open (item 102) | M3, M5 (external contract) as a specialization | the two open certificates; the coupling; a form without published claims if publicity's cost (T3(d)) is not accepted |
| **Policy selection over LI** — Demski 2017; *Conceptual Problems with UDT and Policy Selection*, 2019 | choose a policy at the early market `P_{f(n)}`, `f(n) ≪ n`; claimed to handle counterfactual mugging, ASP, XOR blackmail, transparent Newcomb, Parfit; Troll Bridge listed unsolved; "dirty hack" with no principled `f`; the 2019 post retracts the multi-agent optimism | an early market state ignorant enough to hold the needed correlations | *sketched*: convergence claims with no theorems; *stated*: the free parameter `f(n)` (Soto 2024: the learning-versus-commitment trade-off is structural) | the ideal extension as a proposal; M1 via LI | a theorem for any claimed verdict under the original access — A2 is the matched form for counterfactual mugging, and its recovery domain is the open question of M3 |
| **UDT / FDT** — Dai 2009, 2010; Soares and Fallenstein 2015, arXiv:1507.01986; Yudkowsky and Soares 2017, arXiv:1710.05060; Levinstein and Soares 2020 | policy selection dominates conditioning (informal); FDT's verdicts on Newcomb, transparent Newcomb, Parfit, XOR blackmail, Death in Damascus, twin PD; reflective stability "so far as we know"; first tiling theorems for UDT only in 2025 (Demski, *Understanding Trust*: UDT1.1 prefers no self-modification under policy fairness; UDT1.0 under an added coordination assumption the author calls unjustifiable) | a fixed prior; perfect or graph-specified predictors; "fair" problems, undefined beyond dependence on behaviour | *stated*: logical counterfactuals unspecified ("perhaps the largest open problem"); *illustrated* critiques: Schwarz 2018, MacAskill 2019; Dai 2023 (2TDT-1CDT, commitment races); Macé, Clifton, Kollin 2023 | M5 (self-stability) as a target; none computably | a computable agent with any proved policy-level guarantee — S1/S2/S4 |
| **Proof-based DT / modal agents** — Barasz et al. 2014, arXiv:1401.5577; Critch 2019 (JSL) | Löbian cooperation among modal agents; PrudentBot unexploitable; bounded analogues via parametric bounded Löb | source-code access; PA-provability as the action criterion | *proved* for PD among modal agents; *illustrated*: 5-and-10 spurious proofs; ASP (Slepnev 2011, credited to Drescher) two-boxes | stability for copies only | a bounded, learning analogue; T9 says the BRIA criterion is silent there |
| **Learning in Newcomblike environments** — Bell, Linsefors, Oesterheld, Skalse, NeurIPS 2021 | Thm 2: greedy-in-the-limit, accurate-in-the-limit agents converge only to strongly ratifiable policies; Thm 3: continuous NDPs have one; Thm 6: the repellor problem defeats convergence; optimal policies are not in general ratifiable | policy-dependent transitions and rewards; tabular RL | *proved* as stated | none; a negative baseline for value-based learners | M3's Thm 3-form is what ratifiability lacks: the claim, not the action value, is settled; T4(ii) shows the auction's finite-time cycling has the same shape |
| **Infra-Bayesian decision theory** — Diffractor and Kosoy 2020; Appel and Kosoy, COLT 2025; Gelb 2025 | maximin over a convex set; Newcomb-like problems under pseudocausality; 2025: regret bounds for robust decision-estimation with "Garrabrant-induction-like" beliefs, not tight, efficiency unaddressed | pseudocausality; deterministic policies | *stated*: non-noisy transparent Newcomb fails; efficiency open | a regret form of M3 without an e.c. class | a comparison of no-exploitation coverage with regret bounds on one environment class — not attempted here |
| **Adversarial offer** — Oesterheld and Conitzer 2021 | CDT buys and loses in expectation; abstaining wins; ratificationist repairs fail if the seller can punish randomization | accuracy `3/4`, common knowledge, no randomization | *proved* as a decision-theoretic argument | T1's negative control | — |

**Where restrictions assume away the difficulty.**  (i) BRIA's setting defines no
counterfactual rewards: "accountability for unchosen alternatives" reduces to claims
about executed options, and an improvement no e.c. hypothesis can claim is outside the
criterion by construction.  (ii) ADT's finite agent list and continuous embedders
exclude the infinite-class and discontinuous cases where coverage does its work.  (iii)
FDT's "fair problems" are undefined.  (iv) Policy selection's `f(n)` is a granularity
choice made once by hand; the specialization's block schedule is the same choice as a
declared system parameter with one proved constraint.  (v) Every asymptotic-average
criterion, M3 included, is blind to a single decision; the suite's one-shot rows are
marked invisible.  (vi) **A supplied commitment channel, an oracle, a restricted menu,
or an execution contract is a change of environment**: the suite's lease rows (T4(i),
T6(iii), T7, T8(a)) are conditional results, marked as such, and none counts as
progress on the primary-source problem.  (vii) A worst-case complexity bound on the
agent (Thm 2) is not a statement about its runtime on a benchmark sequence, nor about a
predictor's success frequency there (T8(b)).

## 2. Compatibility of the requirements

| pair | relation |
|---|---|
| M1 with everything | the side-by-side witness satisfies M1–M4 together; only §3's integration excludes it |
| M2(c) with M3 | independent conditions on two outputs of one agent; both relativize to the stream; no conflict |
| M3 (full class, unit level) with commitment (M5) at the unit | **conflict** (P1′): unit-level coverage of the full class excludes a commitment paying outside the scored unit whenever the payoff is e.c.-trackable; resolved by declaring the unit or by restricting `E_rec`, both stated |
| M3 (full class) with the updateless extension (A2) | **conflict** on the environments P1′ covers; the extension needs a recovery domain that is not defined (M3, domain 4) |
| M3 with the strong compatibility form | the implication is unresolved (§5 of the problem statement: a failed derivation, no countermodel); as an added requirement the strong form is consistent with M3 wherever a sound market-reading bidder for the selected option exists on a recognizable test set |
| I1 with M3 | I1 is M3 over `H^P` plus a separation theorem with explicit accounting; no conflict |
| I3 with M4 | M4's tests make the market unbiased on tested rounds, which is exactly what confirms the bad fixed point of A1; I3 asks for more than M4 gives |
| M4 with M5 (self-entered) | a commitment the criterion cannot see is also one no test can refute |
| M5 (external contract) with M3 | the contract is the scored unit; continuation competence assumes it |
| hindsight scoring with M3 | incompatible as stated: needs register (iii); not required |
| S2 with the milestones | consistent only if the counterfactual value agrees with realized feedback wherever both apply — a condition no candidate has stated |

## 3. Unresolved specification choices

Each names the missing definition or choice, its consequence, and which acceptance
judgment it prevents.

1. **The recovery domain of the updateless extension** (M3, domain 4).  Missing: a
   property of the reward process under which myopic optimality and policy optimality
   coincide, stated without reference to the candidate; `E_hist` is too large and
   "choice-independent rewards" too small.  Prevents: certifying an updateless
   candidate as having recovered BRIA where it should (A2).  A specification question;
   research judgment on what the property should be.
2. **The scored unit and who sets it.**  The specialization's schedule is the system's
   and non-dominant; a self-entered contract is open.  Consequence: which commitments
   are representable (T6, T7).  Prevents nothing at the endpoint; shapes the
   specialization.
3. **The commitment source** a candidate is held to (M5).  Consequence: whether
   T6(iii)/T7 verdicts are conditional results or advances.  Prevents: reading any
   channel-dependent verdict as an advance.  Research judgment.
4. **Publicity.**  Of the selection (needed for any feedback theorem about tests) and
   of any estimate (the specialization's choice, with T3(d)'s cost); of internal test
   sets, if a candidate wants a feedback theorem on them.  Consequence: which of §5's
   conditions a candidate can meet.  Research judgment.
5. **The observation-relative inductor** (item 91).  M2(c), W1 and every feedback
   theorem about published selections need it.  A theorem to prove.
6. **Randomization.**  Whether a private random source is a menu option and which
   randomness notion the random-reward clause uses (T5).  Research judgment.
7. **Scope of register (iii).**  Whether one-shot verdicts are wanted at all, or left
   to S2.  Research judgment.
8. **The class `H` exactly.**  Market-reading or blind; whether hypotheses may read
   other hypotheses' claims, wealths, or the winner.  A definition to fix before a
   construction round.
9. **One learner or two.**  A choice learner beside the market (the specialization) or
   the criterion stated inside the market with claims as securities — the item filed
   by the open corrigibility-kernel phase-2 round.  The requirements are neutral.
10. **Trap-free menus.**  M4's named assumption; hypothesis on `E` or duty of the gate.
    Research judgment, with S5 the alternative.
