# Audit: prior approaches, compatibility of the requirements, open specification choices

Labels as in `PROBLEM_STATEMENT.md`.  Citations were checked against the sources on
2026-09-29 by fetching them; where a remembered attribution did not check out, that is
said.  Requirement codes R1–R8 are `PROBLEM_STATEMENT.md` §2.

## 1. Prior approaches: what each guarantees

| approach | guarantee, with quantifiers | assumptions | limitations, by status | requirements met | what would be an advance |
|---|---|---|---|---|---|
| **Logical induction** — Garrabrant, Benson-Tilsen, Critch, Soares, Taylor 2016, arXiv:1609.03543 | No e.c. trader exploits the market (Def. 3.0.1); convergence, calibration and unbiasedness on e.c. subsequences, conditionals, expectations of bounded variables, self-trust (§4), all asymptotic | computable `D̄`; polynomial-time traders; purely epistemic | *proved*: nothing about actions; calibration/unbiasedness only on subsequences the market can identify; *stated by the authors*: no rates | R1 (epistemic), R2, R8(ii) | any action guarantee that consumes the market's expectations without conditioning on untaken actions |
| **LIDT with ε-exploration** — the procedure Garrabrant 2017 ("Two Major Obstacles for Logical Inductor Decision Theory") and Demski and Garrabrant 2018 (*Embedded Agency*, decision theory) describe | none stated; the posts are obstacles: (1) bets conditional on the untaken action never settle, and with exploration a predictor as capable as the agent separates explored from deliberate actions, so the agent learns the wrong counterfactuals and defects/two-boxes; (2) no updatelessness for computations | LI prices; a fixed exploration rate | *illustrated*: 5-and-10 with a capable predictor; counterfactual mugging with a logical coin; *conjectured*: nothing positive | none of R3–R7; identifies R5 and R7 | a testing rule under which a test is a choice (R5's clause), which BRIA supplies |
| **Asymptotic decision theory** — gallabytes 2016 (blog and IAFF; the PDF carries no author line, and the post credits Taylor, Eisenstat and Benson-Tilsen for the ideas — a remembered attribution to other authors did not check out), improved writeup Diffractor 2018 | Thm 2 (2016): soft-argmax over a *finite* list of agents asymptotically dominates the list on a continuous ("fair") embedder, under convergence of the relevant expectations; the 2018 writeup finds the optimality proof flawed (equal utilities do not give equal action distributions) and restates it as **Conjecture 1** under "regret-free" environments | finite agent list; continuous embedders; convergent limits | *illustrated*: ASP one-boxes, Newcomb one-boxes, chicken reaches a mixed equilibrium; counterfactual mugging does not pay; *proved*: nothing beyond fairness of continuous embedders; the 2016 PDF flags its own proof as "a bit suspect" | R1 (limit-computable, given LI); R3 only conjecturally and for finite lists | a proved dominance statement over an infinite e.c. class — which is R3's coverage over `H^P` — with the comparator the claim rather than the embedder's counterfactual |
| **Troll Bridge** — Demski 2019, results due to Eisenstat; *Passing Troll Bridge*, Diffractor 2018 | negative: proof-based DT with the chicken rule, and the probabilistic variant with a `P(cross)=0` clause, refuse to cross by a Löbian proof, whatever the blow-up cost; Diffractor's budget-filtered LI crosses "with arbitrarily high probability" as a stated **conjecture** | the troll reads the *reason* (the consistency of the theory; the clause that fired; the exploration flag) | *proved*: the Löbian refusal; *conjectured*: the budget-filtered fix; *unknown*: the variant where exploration is driven by a source the troll cannot see | none; the family diagnoses R5 | `TEST_SUITE.md` T3: the realized register passes (b), (f) at criterion level, and (c)–(e) are construction- and publicity-dependent; (a) stays in register (iii) |
| **BRIA** — Oesterheld, Demski, Conitzer, TARK 2023, EPTCS 379 pp. 421–440, arXiv:2307.05068 | Def. 7: no overestimation and coverage of every e.c. hypothesis; Thm 1: a BRIA covering a c.e. class of `O(g)`-computable hypotheses is `O(g q)`-computable (first-price auction); Thm 2: not `O(g)`-computable; Thm 3: an efficiently identifiable option with an e.c. lower bound is matched on average; Thm 4: boundedly vMWC-random rewards with e.c. means are attained; Thm 5: folk theorem, with randomization; App. C: Hannan consistency unachievable and undesirable (a Newcomb variant); App. D: estimates are necessary against biased testing | finite menus; rewards of the chosen option only; `DP_t` may depend on past choices; myopic target | *stated by the authors*: myopia; counterfactual rewards undefined; limit statements only; no coherence à la LI (open question); no policy-level result (combinatorial auctions, one footnote); ignores the ability to randomize; *proved here*: estimates are not beliefs (P2, `test_cm`); the first-price auction is trapped by the tentative troll while the criterion is met (T3(d)) | R1, R3, R5, R7(b),(d) at unit granularity; R6/R7(a) via the continuation form in this repository | R2(c)+R4 with the class `H^P` (the coupling the paper's §8 conjectures: "Garrabrant inductors with (pseudo-)randomization could be used to construct BRIAs"), and the block form's policy frontier |
| **Continuation BRIA** — `wiki/Continuation-BRIA.md`; round `projects/deference/rounds/2026-09-08-continuation-bria/` | the weighted criterion; existence iff non-dominance of the system schedule, with the prefix subsidy rule; continuation competence under (BR); `Regret = SHIFT + SLACK + LEARN` exact; regret against all legitimate policies false | system-scheduled horizons; realized gated execution; opening-timed subsidy | *derived on Lean algebra*, unregistered; `SHIFT`/`SLACK` certificates open (item 86); the LI coupling open (item 102) | R6, R7(a),(c) partially | the two open certificates; the coupling |
| **Policy selection over LI** — Demski 2017 ("Policy Selection Solves Most Problems"); *Conceptual Problems with UDT and Policy Selection*, 2019 | choose a policy at the early market `P_{f(n)}`, `f(n) ≪ n`, for how to use `P_n`; claimed to handle counterfactual mugging, ASP, XOR blackmail, transparent Newcomb, Parfit; Troll Bridge listed as unsolved; the author calls it a "dirty hack" with no principled `f`; the 2019 post retracts the multi-agent optimism | an early market state ignorant enough to hold the needed correlations | *sketched*: convergence claims in the LI framework, no theorems with quantifiers; *stated*: the free parameter `f(n)` (Soto 2024 finds the learning-versus-commitment trade-off structural) | R7(c) as a proposal; R1 via LI | a principled granularity — which is the block schedule question of §3 here, with non-dominance as its one known constraint |
| **UDT / FDT** — Dai 2009, 2010 (UDT1.0/1.1); Soares and Fallenstein 2015, arXiv:1507.01986; Yudkowsky and Soares 2017, arXiv:1710.05060; Levinstein and Soares 2020 | policy selection dominates conditioning (informal); FDT's verdicts on Newcomb, transparent Newcomb, Parfit, XOR blackmail, Death in Damascus, twin PD; reflective stability "so far as we know"; first tiling theorems for UDT only in 2025 (Demski, *Understanding Trust*: UDT1.1 prefers no self-modification under policy fairness; UDT1.0 under an added coordination assumption the author calls unjustifiable) | a fixed prior; perfect or graph-specified predictors; "fair" problems, undefined beyond dependence on behaviour | *stated*: logical counterfactuals unspecified ("perhaps the largest open problem"); *illustrated* critiques: Schwarz 2018, MacAskill 2019 (Bomb; the predictor need not run the agent's algorithm); Dai 2023 (2TDT-1CDT, commitment races); Macé, Clifton, Kollin 2023 (optimality and unexploitability incompatible under awareness growth) | R7 as targets; none computably | a computable agent with any proved policy-level guarantee — S1/S2 here |
| **Proof-based DT / modal agents** — Barasz et al. 2014, arXiv:1401.5577; Critch 2019 (JSL) | Löbian cooperation: FairBot cooperates with FairBot (PA ⊢), PrudentBot unexploitable and cooperates with itself and FairBot; modal-agent outcomes decidable in GL; bounded analogues via parametric bounded Löb | source-code access; PA-provability as the action criterion | *proved* for PD among modal agents; *illustrated*: 5-and-10 spurious proofs; ASP (Slepnev 2011, credited to Drescher) two-boxes | R7(d) for copies only | a bounded, learning analogue; T9 says the BRIA criterion is silent there |
| **Learning in Newcomblike environments** — Bell, Linsefors, Oesterheld, Skalse, NeurIPS 2021 | Thm 2: a model-free, greedy-in-the-limit, accurate-in-the-limit agent converges (if at all) only to strongly ratifiable policies; Thm 3: continuous NDPs have one; Thm 6: the repellor problem defeats convergence for any infinitely exploring softmax-type agent; optimal policies are not in general ratifiable (one-boxing is not) | policy-dependent transitions and rewards; tabular RL | *proved* as stated; frequencies in LARPS conjectured | none; a negative baseline for value-based learners | R3's Thm 3-form is exactly what ratifiability lacks: the claim, not the action value, is what is settled — and T4(ii) shows the auction's finite-time cycling has the same shape |
| **Infra-Bayesian decision theory** — Diffractor and Kosoy 2020; Appel and Kosoy, COLT 2025 (decision-estimation regret with "Garrabrant-induction-like" beliefs); Gelb 2025 (supra-POMDP Newcomb variants) | maximin over a convex set; Newcomb-like problems under pseudocausality; 2025: regret bounds for robust decision-estimation, not tight, efficiency unaddressed | pseudocausality; deterministic policies | *stated*: transparent Newcomb (non-noisy) fails; efficiency open | a regret form of R3 without an e.c. class | a comparison of no-exploitation coverage with regret bounds on one environment class — not attempted here |
| **Adversarial offer** — Oesterheld and Conitzer 2021 (*Phil. Quarterly*) | CDT buys and loses in expectation; abstaining wins; ratificationist repairs fail if the seller can punish randomization | accuracy `3/4`, common knowledge, no randomization | *proved* as a decision-theoretic argument | T1's negative control | — |

**Where restrictions assume away the difficulty.**  (i) BRIA's setting defines no
counterfactual rewards: "accountability for unchosen alternatives" reduces to claims
about executed continuations, and an improvement that no e.c. hypothesis can claim is
outside the criterion by construction — the specification keeps that boundary explicit
rather than hiding it (R5, R8's hindsight gap).  (ii) ADT's finite agent list and
continuous embedders exclude the infinite-class and discontinuous cases where coverage
does its work.  (iii) FDT's "fair problems" are undefined, so its dominance claim has no
comparator class.  (iv) Policy selection's `f(n)` is the granularity choice made once,
by hand; the block schedule here makes the same choice as a declared system parameter
with one proved constraint.  (v) Every asymptotic-average criterion, including R3, is
blind to a single decision; the suite's one-shot rows are marked invisible instead of
being scored by a proxy.

## 2. Compatibility of the requirements

| pair | relation |
|---|---|
| R1 with everything | the side-by-side witness satisfies R1, R2, R3, R5 together; only R4 and T10 exclude it |
| R2(c) with R3 | independent conditions on two outputs of one agent; both relativize to the stream; no conflict |
| R3 with R4, per round | **conflict** with cross-round commitment (P1): together they force asymptotic myopia at the scoring granularity; resolved by declaring the granularity (§3 of the problem statement), which leaves cross-block commitment out |
| R4 with R5 | R5's tests are what make the market unbiased on the tested subsequence; R4's lower half *is* coverage with market-reading hypotheses |
| R5 with R7(c) | a cross-block commitment the criterion cannot see is also one no test can refute — the same boundary from both sides |
| R6 with R7(a) | the lease is the block; continuation competence assumes it |
| R7(d) with R8 | a rival rule reading a stronger market is still a hypothesis in `H^P`; covered within blocks |
| R8 hindsight with R3 | incompatible as stated: re-scoring an executed block against an unexecuted continuation needs register (iii); dropped from the minimum |
| S2 with the minimum | consistent only if the counterfactual value agrees with realized feedback wherever both apply — a consistency condition no candidate has stated |

## 3. Unresolved specification choices

Each names the missing definition or choice, its consequence, and who decides.

1. **Scoring granularity and schedule authority.**  The block schedule is the system's
   and non-dominant (`m_K / S_K → 0`, the one proved constraint); whether bidders may
   request horizons and how duration is allocated is open (`wiki/Continuation-BRIA.md`
   §9).  Consequence: which commitments are representable (T6, T7).  Research judgment.
2. **Lease publicity.**  What predictors and other agents may read: the published
   selection, the published estimate, the winning index, or a bounded simulation of the
   agent.  Consequence: T3(d), T4, T7, T8 verdicts.  The realized register treats the
   published outputs as public state; whether the *estimate* is public is a design
   choice with a known cost (the tentative troll).  Research judgment.
3. **The observation-relative inductor.**  R2(c) and R4 need LI's theorems relative to
   an observation stream (`PRIORITIES.md` item 91).  Consequence: without it the minimum
   falls back to R2(b) and R4 holds only for block scores decided by `Γ`.  A theorem to
   prove, not a choice.
4. **Randomization.**  Whether a private random source is a menu option and which
   randomness notion the criterion's random-reward clause uses (vMWC relative to the
   class, as in the paper, or true randomness).  Consequence: T5.  Research judgment.
5. **Scope of register (iii).**  Whether the program wants one-shot verdicts from a
   synthesis at all, or leaves them to S2.  The minimum recommends leaving them out;
   every candidate in §1 that claims them claims them without a theorem.  Research
   judgment.
6. **The class `H^P` exactly.**  Hypotheses read the published prices; whether they may
   also read other hypotheses' claims, the wealths, or the winner (the paper's Thm 2
   diagonal hypothesis reads the agent's choice) changes what coverage forces.
   Consequence: the strength of R5 and R7(d).  A definition to fix before a
   construction round.
7. **One learner or two.**  Whether the synthesis keeps a choice learner beside the
   market (Continuation BRIA's shape) or states the BRIA criterion inside the market
   with claims as securities settled on choice — the item filed by the open
   corrigibility-kernel phase-2 round.  The specification is neutral: R4 is what the
   two-learner shape must prove and what the one-learner shape would make
   definitional; T10 and T11 score both.  A construction choice, not a judgment.
8. **Trap-free menus.**  R5's named assumption; whether it is a hypothesis on `E` or a
   duty of the gate (the deference line's admissibility) is an allocation between lines.
   Research judgment, with S5 the alternative.
