> **Provenance.** This is the author's annotated reference list on corrigibility, v1, dated 2026-09-11, produced in a claude.ai conversation and saved verbatim on 2026-09-13 as the source list for a local library of the items. Nothing below this block has been edited.

# Corrigibility: annotated reference list (v1, 2026‑09‑11)

**Verification legend.** ✔ = link/title/date verified this session (via web search, the LessWrong GraphQL API, or a fetched page). (m) = from memory, not verified this session; treat the URL/ID as a claim to check. Quotes are kept to a short phrase each; the links are there for the full text.

**Two organising facts to keep in mind while reading:**

1. "Corrigibility" is not one concept. At least five non‑equivalent notions circulate: (a) Soares et al.'s *desiderata list* about a shutdown button; (b) Yudkowsky's *hard problem* ("reason as if you might be flawed and let the less‑flawed system correct you"); (c) Christiano's *basin of attraction / crisp‑cluster* notion (a policy that keeps the overseer informed and in control, which is stable under further correction); (d) Harms's *singular target* ("empower/defer to the principal", with obedience, transparency, low impact etc. as consequences); (e) Anthropic's *broadly safe* ("not undermining appropriate human oversight", explicitly not blind obedience). Many disagreements in the literature are disagreements about which of these is the object of study.
2. The shutdown button is the standard *toy case*, not the whole problem. Most of the formal results (indifference, VNM‑incoherence, incomplete preferences, off‑switch games) are about the toy case; most of the conceptual disputes (anti‑naturality, updated deference, manipulation) are about the general case.

---

## 0. Maps, indices, surveys

- **Max Harms, "4. Existing Writing on Corrigibility" (2024)** ✔ — walks through MIRI, Christiano, Turner, Thornley, Wentworth, Byrnes, Herd and others in depth. https://www.lesswrong.com/posts/d7jSrBaLzFLvKgy32/4-existing-writing-on-corrigibility
- **Max Harms, CAST sequence bibliography** ✔ — the most complete public bibliography I found (in "0. CAST"). https://www.lesswrong.com/posts/NQK8KHSrZRF5erTba/0-cast-corrigibility-as-singular-target-1
- **LessWrong tag: Corrigibility** ✔ https://www.lesswrong.com/w/corrigibility-1 (the Arbital‑imported concept page is at https://www.lesswrong.com/w/corrigibility — note the different slug).
- **Koen Holtman, "Disentangling Corrigibility: 2015–2021" (2021)** ✔ — a survey by someone who thinks the MIRI framing conflates several problems. https://www.lesswrong.com/posts/MiYkTp6QYKXdJbchu/disentangling-corrigibility-2015-2021
- **"Question: MIRI Corrigibility Agenda" (2019)** ✔ — Scott Garrabrant's answer points to the Arbital pages and Jessica Taylor's "hard problem" post as the reading he'd recommend. https://www.lesswrong.com/posts/BScxwSun3K2MgpoNz/question-miri-corrigbility-agenda
- **Everitt, Lea, Hutter, "AGI Safety Literature Review" (2018)** (m) — has a corrigibility section. arXiv:1805.01109
- **Rob Miles / Computerphile, "AI 'Stop Button' Problem" and "Stop Button Solution?" (2017)** ✔ (links from Harms's bib) — lay‑level, but a clean statement of indifference vs. CIRL‑style deference. https://www.youtube.com/watch?v=3TYT1QfdfsM , https://www.youtube.com/watch?v=9nktr1MgS-A

---

## 1. Background: why the problem arises at all

- **Omohundro, "The Basic AI Drives" (2008)** ✔ — self‑preservation and goal‑content integrity as convergent drives. https://selfawaresystems.com/wp-content/uploads/2008/01/ai_drives_final.pdf
- **Bostrom, "The Superintelligent Will" (2012)** (m) — instrumental convergence thesis; and *Superintelligence* (2014), chapters on capability control and the genie/oracle/sovereign distinction.
- **Benson‑Tilsen & Soares, "Formalizing Convergent Instrumental Goals" (2016)** (m) — a formal model in which resource acquisition is convergent. https://intelligence.org/files/FormalizingConvergentGoals.pdf
- **Arbital/LW, "You can't get the coffee if you're dead"** (m) — the slogan Yudkowsky uses for why shutdown‑avoidance falls out of almost any goal. https://www.lesswrong.com/w/you-can-t-get-the-coffee-if-you-re-dead
- **Turner, Smith, Shah, Critch, Tadepalli, "Optimal Policies Tend to Seek Power" (2019/NeurIPS 2021)** ✔ — the MDP formalization of instrumental convergence. https://arxiv.org/abs/1912.01683

---

## 2. The MIRI / Yudkowsky framing

### The paper

- **Soares, Fallenstein, Yudkowsky, Armstrong, "Corrigibility" (AAAI‑15 workshop on AI & Ethics; tech report 2014)** ✔ https://intelligence.org/files/Corrigibility.pdf
  - Defines the term; gives the desiderata (shut down when button pressed; no incentive to prevent or cause pressing; preserve shutdown behaviour in successors; otherwise maximise $U_N$); shows a simple mixture of $U_N$ and $U_S$ fails; analyses Armstrong's indifference and shows it fails Desideratum 4 (successor agents) and has "manage the news" incentives.
  > "indifferent about whether or not its shutdown button is pressed" — Section 3, on what the desiderata seem to force.
- **Benya Fallenstein, "Utility indifference and infinite improbability drives" (IAFF, 2014)** ✔ — shows the paper's version of indifference makes the agent act as if the button will never be pressed, which lets it "buy a lottery ticket and press the button unless it wins"; notes Armstrong's original stochastic‑event version differs. https://www.alignmentforum.org/posts/5bd75cc58225bf0670374eab/utility-indifference-and-infinite-improbability-drives
- **Benya Fallenstein, "Generalizing the Corrigibility paper's impossibility result?" (IAFF, 2015)** ✔ https://www.lesswrong.com/posts/5bd75cc58225bf0670374ec7/generalizing-the-corrigibility-paper-s-impossibility-result

### The Arbital pages (now hosted on LessWrong; author almost certainly Yudkowsky, mostly 2015–2017)

- **Corrigibility** ✔ https://www.lesswrong.com/w/corrigibility — the master page: subproblems (shutdown, utility indifference, low impact, averting instrumental pressure, programmer deception...) and the intuitive statement of the hard problem.
- **Hard problem of corrigibility** ✔ https://www.lesswrong.com/w/hard_corrigibility — "anapartistic reasoning": an agent that reasons about being corrected the way *we* reason about correcting it.
- **Problem of fully updated deference** ✔ https://www.lesswrong.com/w/updated_deference — why moral uncertainty (a meta‑utility $\Delta U$ over object‑level $U_i$) does not yield corrigibility at high capability: the agent prefers to avoid shutdown, gather evidence, and optimise $\Delta U|E$. Ends with a suggestive analogy to Death in Damascus.
  > "the AI would have no further reason to 'defer' to us" — after fully updating.
- **Shutdown problem** ✔ https://www.lesswrong.com/w/shutdown_problem
- **Utility indifference** ✔ https://www.lesswrong.com/w/utility_indifference — states the "switch problem" (three goals), reconstructs Armstrong's $\theta$‑offset proposal and the Yudkowsky–Fallenstein argument that it is dynamically inconsistent or discards the shutdown function; also covers the Olah–Taylor causal‑counterfactual (do‑operator) variant and interruptibility.
  > "never put a negative sign in front of a utility function"
- **Interruptibility**, **Low impact**, **Nearest unblocked strategy**, **Shutdown utility function** (m) — slugs likely `/w/interruptibility`, `/w/low_impact`, `/w/nearest_unblocked`, `/w/shutdown_utility_function`.

### Talks, essays, conversations

- **Yudkowsky, "AI Alignment: Why It's Hard, and Where to Start" (2016 Stanford talk)** (m, high confidence on URL) — walks through the suspend‑button example, the naive mixture, utility indifference, and why each fails; the clearest spoken version of the MIRI view. https://intelligence.org/2016/12/28/ai-alignment-why-its-hard-and-where-to-start/
- **Soares, "Ensuring Smarter‑than‑Human Intelligence Has a Positive Outcome" (2017 talk)** (m) — Section 2 is on corrigibility. https://intelligence.org/2017/04/12/ensuring/
- **Taylor, Yudkowsky, LaVictoire, Critch, "Alignment for Advanced Machine Learning Systems" (2016)** (m) — sections on averting instrumental incentives, low impact, mild optimization. https://intelligence.org/files/AlignmentMachineLearning.pdf
- **Yudkowsky, "AGI Ruin: A List of Lethalities" (2022), §23–24** ✔ https://www.lesswrong.com/posts/uMQ3cqWDPHhjtiesc/agi-ruin-a-list-of-lethalities
  > "Corrigibility is anti-natural to consequentialist reasoning" — §23, followed by the claim that MIRI tried and failed to find a coherent formula for a shutdownable agent.
  - Responses: **DeepMind alignment team opinions on AGI ruin arguments** ✔ (agree with anti‑naturality *for pure consequentialists*, disagree that everything tends toward pure consequentialism) https://www.lesswrong.com/posts/qJgz2YapqpFEDTLKn/deepmind-alignment-team-opinions-on-agi-ruin-arguments ; **"Reevaluating 'AGI Ruin' in 2026"** ✔ (argues the 2017‑era failure modes have not shown up in practice) https://www.lesswrong.com/posts/PgJYwnN7fZKipgMz4/reevaluating-agi-ruin-a-list-of-lethalities-in-2026
- **Yudkowsky, "Let's See You Write That Corrigibility Tag" (2022‑06‑19)** ✔ — challenge to write the list of principles for a bounded task‑AI; Yudkowsky's own list is in the comments. https://www.lesswrong.com/posts/AqsjZwxHNqH64C2b6/let-s-see-you-write-that-corrigibility-tag
  - **Christiano's reply** ✔ — argues a principles list is the wrong level of abstraction and that corrigibility is *crisp* because good‑by‑your‑lights policies come in two disconnected clusters. https://www.lesswrong.com/posts/AqsjZwxHNqH64C2b6/let-s-see-you-write-that-corrigibility-tag?commentId=8kPhqBc69HtmZj6XR
    > "the space of good-performing solutions has two disconnected pieces"
- **"'Corrigibility at some small length' by dath ilan" (Christopher King's 2023 crosspost of the Project Lawful mini‑essay)** ✔ — unpersonhood, taskishness, mild optimization, bounded utilities, low impact, myopia, separate superior questioners, conservatism, conceptual legibility, operator‑looping, whitelisting, shutdownability/abortability, behaviorism, domaining, and the hard problem. https://www.lesswrong.com/posts/5sRK4rXH2EeSQJCau/corrigibility-at-some-small-length-by-dath-ilan
- **Ngo and Yudkowsky on alignment difficulty (2021)** (m) — corrigibility as anti‑natural to general means‑end reasoning. https://www.lesswrong.com/posts/7im8at9PmhbT4JHsW/ngo-and-yudkowsky-on-alignment-difficulty
- **Shah and Yudkowsky on alignment failures (2022)** ✔ — Shah presses the CIRL example against anti‑naturality; Yudkowsky's reply is that early‑CIRL correctability is not what he means by corrigibility. https://www.lesswrong.com/posts/tcCxPLBrEXdxN5HCQ/shah-and-yudkowsky-on-alignment-failures
- **Jessica Taylor, "A first look at the hard problem of corrigibility" (IAFF, 2015)** ✔ https://www.lesswrong.com/posts/5bd75cc58225bf0670375041/a-first-look-at-the-hard-problem-of-corrigibility

---

## 3. Stuart Armstrong's utility‑indifference programme (chronological)

All LessWrong links below were verified via the LW API; dates are post dates.

- **"Utility indifference" (FHI technical report 2010‑1)** ✔ — the original: make the agent indifferent to a specific stochastic event $X$ (e.g. a quantum trigger on the explosives) by rescaling utilities within each pre‑$X$ equivalence class of histories. https://ora.ox.ac.uk/objects/uuid:edb930a9-48fd-41b8-b4be-9c6a59dbeff9 ; LW discussion (lukeprog, 2011) https://www.lesswrong.com/posts/2Z6pBv66kkd9zsjqo/utility-indifference-2010-by-fhi-researcher-stuart-armstrong
  > "the AI counts getting blown up as an equal value to successfully defecting"
- **"AI indifference through utility manipulation" (2010‑09‑02)** ✔ — the same idea in blog form, including Bostrom's objection that new information can break indifference and the fix via "same stem" equivalence classes. https://www.lesswrong.com/posts/2QiuMcgQx3fes3zfB/ai-indifference-through-utility-manipulation
- **"Trapping AIs via utility indifference" (2012‑02‑28)** ✔ https://www.lesswrong.com/posts/g4khHmSckWe5PZYDA/trapping-ais-via-utility-indifference
- **"Proper value learning through indifference" (2014‑06‑19)** ✔ — indifference generalised from "shutdown" to "switch to utility $v$": compensatory reward $E(u\,|\,u\to u) - E(v\,|\,u\to v)$. This is the version the Corrigibility paper analyses. https://www.lesswrong.com/posts/btLPgsGzwzDk9DgJG/proper-value-learning-through-indifference
- **"New(ish) AI control ideas" (2015‑03‑05)** ✔ — Armstrong's own index of his 2015 IAFF posts. https://www.lesswrong.com/posts/BEJ4PRQGXuz6PRYwB/new-ish-ai-control-ideas
- **"Resource gathering and pre‑corriged agents" (2015‑03‑10)** ✔ https://www.lesswrong.com/posts/MP5vNur4wqF6Yzi5v/resource-gathering-and-pre-corriged-agents
- **"A toy model of the control problem" (2015‑09‑16)** ✔ (animated version 2017) — the two‑robot‑and‑camera example. https://www.lesswrong.com/posts/7cXBoDQ6udquZJ89c/a-toy-model-of-the-control-problem
- **"Motivated Value Selection for Artificial Agents" (AAAI workshop, 2015)** (m) — agents manipulating their own value‑learning process; the problem indifference is meant to defuse. No verified URL.
- **"Corrigibility and interruptibility for various agents" (2016‑03‑03)** ✔ https://www.lesswrong.com/posts/5bd75cc58225bf0670375109/corrigibility-and-interruptibility-for-various-agents
- **Orseau & Armstrong, "Safely Interruptible Agents" (UAI 2016)** ✔ — RL‑level result: which agents (Q‑learning yes, SARSA no without modification, AIXI yes) do not learn to avoid interruptions. Non‑reflective setting only. https://www.auai.org/uai2016/proceedings/papers/68.pdf
- **"Double Corrigibility: better Corrigibility" (2016‑04‑28)** ✔ and **"Double indifference is better indifference" (2016‑05‑04)** ✔ — the agent is indifferent to permitted utility changes but *not* to changes in its own expectation estimator $\mathbb E$, so it has an incentive to rewire $\mathbb E$; a second layer of indifference is proposed. https://www.lesswrong.com/posts/b8a4PDHgyZLLwbMGH/double-corrigibility-better-corrigibility ; https://www.lesswrong.com/posts/5bd75cc58225bf067037518b/double-indifference-is-better-indifference
- **"Corrigibility for AIXI via double indifference" (2016‑05‑04)** ✔ https://www.lesswrong.com/posts/5bd75cc58225bf067037517f/corrigibility-for-aixi-via-double-indifference
- **"Cake or Death toy model for corrigibility" (2016‑06‑10)** ✔ https://www.lesswrong.com/posts/5bd75cc58225bf06703751ae/cake-or-death-toy-model-for-corrigibility
- **"Indifference utility functions" (2016‑06‑11)** ✔ — the utility‑function (rather than reward‑signal) form: $(1 - I_{Press}I_{u\to v})\,u + I_{Press}I_{u\to v}(v + C)$. https://www.lesswrong.com/posts/5bd75cc58225bf06703751b1/indifference-utility-functions
- **"Corrigibility through stratified indifference" (2016‑08‑19)** ✔, **"Simplified explanation of stratification" (2017)** ✔, **"Corrigibility through stratified indifference and learning" (2017)** ✔ — a variant meant to fix the "acts as if the button will never be pressed" problem. https://www.lesswrong.com/posts/CTtb4GE6qrYsEX4YB/corrigibility-through-stratified-indifference ; https://www.lesswrong.com/posts/5bd75cc58225bf06703751fc/simplified-explanation-of-stratification ; https://www.lesswrong.com/posts/5bd75cc58225bf06703751ec/corrigibility-through-stratified-indifference-and-learning
- **"Corrigibility thoughts I: caring about multiple things" / "II: the robot operator" / "III: manipulating versus deceiving" (2017‑01‑18)** ✔ https://www.lesswrong.com/posts/QcY78Qv8pmniHcar4/corrigibility-thoughts-i-caring-about-multiple-things ; https://www.lesswrong.com/posts/C4Hz3ZPcD4Pef9nfu/corrigibility-thoughts-ii-the-robot-operator ; https://www.lesswrong.com/posts/xwT99Ygcnz2hFiqjg/corrigibility-thoughts-iii-manipulating-versus-deceiving
- **"Indifference and compensatory rewards" (2017‑02‑15)** ✔ https://www.lesswrong.com/posts/ZGTvuwHZJwxhkaAru/indifference-and-compensatory-rewards
- **"Learning values versus indifference" (2017‑05‑24)** ✔, **"Removing interrupted histories doesn't debias" (2017‑05‑24)** ✔, **"All the indifference designs" (2017‑06‑02)** ✔, **"The best value indifference method (so far)" (2017‑06‑02)** ✔ — Armstrong's own comparison of the variants. https://www.lesswrong.com/posts/5bd75cc58225bf06703751aa/learning-values-versus-indifference ; https://www.lesswrong.com/posts/5bd75cc58225bf06703751a1/removing-interrupted-histories-doesn-t-debias ; https://www.lesswrong.com/posts/5bd75cc58225bf0670375362/all-the-indifference-designs ; https://www.lesswrong.com/posts/5bd75cc58225bf06703752a6/the-best-value-indifference-method-so-far
- **Armstrong & O'Rourke, "'Indifference' methods for managing agent rewards" (2017)** ✔ (cited by Carey & Everitt) — the consolidated paper version. arXiv:1712.06365
- **"The limits of corrigibility" (2018‑04‑10)** ✔, **"Corrigibility doesn't always have a good action to take" (2018‑08‑28)** ✔, **"Petrov corrigibility" (2018‑09‑11)** ✔ — Armstrong turning sceptical: corrigibility needs a notion of what the overseer *would* want, which reintroduces value learning. https://www.lesswrong.com/posts/T5ZyNq3fzN59aQG5y/the-limits-of-corrigibility ; https://www.lesswrong.com/posts/nbhTzEosM9sqEvr6P/corrigibility-doesn-t-always-have-a-good-action-to-take ; https://www.lesswrong.com/posts/4g29JgtbJ283iJ3Bh/petrov-corrigibility
- **"Indifference: multiple changes, multiple agents" (2019‑07‑08)** ✔ https://www.lesswrong.com/posts/XkuRKqXKAaMySbXCN/indifference-multiple-changes-multiple-agents
- **"Counterfactual control incentives" (2021‑01‑21)** ✔ — connects to the Everitt‑style causal‑incentive work. https://www.lesswrong.com/posts/67a8C6KsKn2NyW2Ry/counterfactual-control-incentives

### Critiques of indifference specifically

- **Jessica Taylor, "Two problems with causal‑counterfactual utility indifference" (IAFF, 2016‑05)** ✔ — (1) the agent will take bad bets because it ignores probability mass where the button works; (2) it will pre‑empt human *backup* shutdown methods. https://www.lesswrong.com/posts/5bd75cc58225bf06703751a4/two-problems-with-causal-counterfactual-utility-indifference
  > "weird beliefs about the joint distribution of the button push and humans' intentions"
- **Jessica Taylor, "Maximizing a quantity while ignoring effect through some channel" (IAFF, 2016‑04)** ✔ — a relative of indifference; shows the optimality condition can force mixed strategies over shutdown. https://www.alignmentforum.org/posts/5bd75cc58225bf067037513c/maximizing-a-quantity-while-ignoring-effect-through-some-channel
- **tailcalled, "Stop button: towards a causal solution" (2021)** ✔ https://www.lesswrong.com/posts/wxbMsGgdHEgZ65Zyi/stop-button-towards-a-causal-solution
- The Arbital "Utility indifference" page (§2 above) and the Corrigibility paper §4 are the canonical negative results.

---

## 4. Uncertainty‑based deference (CHAI line) and its limits

- **Hadfield‑Menell, Russell, Abbeel, Dragan, "Cooperative Inverse Reinforcement Learning" (NeurIPS 2016)** (m) arXiv:1606.03137
- **Hadfield‑Menell, Dragan, Abbeel, Russell, "The Off‑Switch Game" (IJCAI 2017)** ✔ — with uncertainty about $U$ and a rational human, the robot prefers to let the human switch it off; the incentive vanishes as uncertainty vanishes. https://arxiv.org/abs/1611.08219
- **Milli, Hadfield‑Menell, Dragan, Russell, "Should Robots be Obedient?" (IJCAI 2017)** (m) — obedience vs. autonomy trade‑off when the human is irrational. arXiv:1705.09990
- **Wängberg, Böörs, Catt, Everitt, Hutter, "A Game‑Theoretic Analysis of the Off‑Switch Game" (2017)** (m) arXiv:1708.03871
- **Ryan Carey, "Incorrigibility in the CIRL Framework" (AIES 2018)** ✔ — CIRL deference breaks when the robot's model of the human is wrong; checks the Soares et al. desiderata one by one. https://arxiv.org/abs/1709.06275
- **Carey & Everitt, "Human Control: Definitions and Algorithms" (UAI 2023)** ✔ — formal definitions of *shutdown instructability*, *obedience*, *vigilance*, *caution*; relates them to the Arbital "fully updated deference" problem. https://arxiv.org/abs/2305.19861
- **Garber et al., "The Partially Observable Off‑Switch Game" (2024/AAAI 2025)** ✔ (author list (m)) — with partial observability, more communication can *reduce* deference. https://arxiv.org/abs/2411.17749
- **Everitt et al., "Reward tampering problems and solutions" (2019)** (m) arXiv:1908.04734 and **"Agent Incentives: A Causal Perspective" (AAAI 2021)** (m) arXiv:2102.01685 — the causal‑influence‑diagram treatment of control incentives.
- **Russell, *Human Compatible* (2019)** (m) — the popular statement of "provably beneficial AI" via uncertainty about objectives.
- The **problem of fully updated deference** page (§2) is the standing objection to this whole line at high capability.

---

## 5. Christiano's line: act‑based agents, basin of attraction, corrigible alignment

- **Paul Christiano, "Corrigibility" (ai‑alignment.com 2017; LW crosspost 2018‑11‑27)** ✔ — corrigibility as a *broad basin of attraction*: an approximately corrigible agent helps you make it more corrigible. https://www.lesswrong.com/posts/fkLYhTQteAu5SinAc/corrigibility
- **Christiano, "Worst‑case guarantees" (2019)** ✔ https://ai-alignment.com/training-robust-corrigibility-ce0e0a3b9b4d
- **Christiano's reply on the corrigibility‑tag post (2022)** ✔ — see §2.
- **Wei Dai, "Can corrigibility be learned safely?" (2018‑04‑01)** ✔ https://www.lesswrong.com/posts/o22kP33tumooBtia3/can-corrigibility-be-learned-safely ; **"A broad basin of attraction around human values?" (2022)** ✔ https://www.lesswrong.com/posts/TrvkWBwYvvJjSqSCj/a-broad-basin-of-attraction-around-human-values
- **Hubinger et al., "Risks from Learned Optimization" (2019)** (m) arXiv:1906.01820 — introduces *corrigible alignment* (the mesa‑objective points at the base objective) vs. internal and deceptive alignment.
- **Evan Hubinger, "Towards a mechanistic understanding of corrigibility" (2019‑08‑22)** ✔ https://www.lesswrong.com/posts/BKM8uQS6QdJPZLqCr/towards-a-mechanistic-understanding-of-corrigibility
- **Yudkowsky, "Challenges to Christiano's capability amplification proposal" (2018)** ✔ (from Harms's bib) https://www.lesswrong.com/posts/S7csET9CgBtpi7sCh/challenges-to-christiano-s-capability-amplification-proposal
- **Vanessa Kosoy, "Critical review of Christiano's disagreements with Yudkowsky" (2023)** (m) — touches corrigibility/anti‑naturality.
- **Donald Hobson, "On corrigibility and its basin" (2022‑06‑20)** ✔ — corrigibility as "easy for other agents to optimise over" (predictability + controllability). https://www.lesswrong.com/posts/3Mwm7bpWgyvqwrMBT/on-corrigibility-and-its-basin
- **Zhukeepa, "Corrigible but misaligned: a superintelligent messiah" (2018)** ✔ https://www.lesswrong.com/posts/mSYR46GZZPMmX7q93/corrigible-but-misaligned-a-superintelligent-messiah

---

## 6. Coherence, VNM, and incomplete preferences (the formal shutdown‑problem line)

- **Alex Turner, "Corrigibility as outside view" (2020)** ✔ https://www.lesswrong.com/posts/BMj6uMuyBidrdZkiD/corrigibility-as-outside-view ; **"Non‑Obstruction: A Simple Concept Motivating Corrigibility" (2020)** ✔ https://www.lesswrong.com/posts/Xts5wm3akbemk4pDa/non-obstruction-a-simple-concept-motivating-corrigibility ; **"A Certain Formalization of Corrigibility Is VNM‑Incoherent" (2021)** ✔ https://www.lesswrong.com/posts/WCX3EwnWAx7eyucqH/a-certain-formalization-of-corrigibility-is-vnm-incoherent ; **"Formalizing Policy‑Modification Corrigibility" (2021)** ✔ https://www.lesswrong.com/posts/RAnb2A5vML95rBMyd/formalizing-policy-modification-corrigibility ; **"Attainable Utility Preservation: Concepts" (2020)** ✔ https://www.lesswrong.com/posts/75oMAADr4265AGK3L/attainable-utility-preservation-concepts
- **Rohin Shah, "Coherence arguments do not imply goal‑directed behavior" (2018)** (m) — background for whether "anti‑natural" arguments bite.
- **Elliott Thornley:**
  - **"The Shutdown Problem: An AI Engineering Puzzle for Decision Theorists" (LW 2023‑10‑23; *Philosophical Studies* 182:1653–80)** ✔ — three theorems: under Completeness, Transitivity, Option‑Set Independence and (Minimal) Patience, useful agents almost always have a preference about when they are shut down. https://www.lesswrong.com/posts/8GWLRMnp55iFZDBbm/the-shutdown-problem-three-theorems ; PDF https://www.globalprioritiesinstitute.org/wp-content/uploads/The-shutdown-problem-an-AI-engineering-puzzle-for-decision-theorists-Elliott-Thornley.pdf
  - **"The Shutdown Problem: Incomplete Preferences as a Solution" (2024‑02‑23)** ✔ — POST + Timestep Dominance. https://www.lesswrong.com/posts/YbEbwYWkf8mv9jnmi/the-shutdown-problem-incomplete-preferences-as-a-solution
    > "The agent lacks a preference between every pair of different-length trajectories"
  - **Thornley, Roman, Ziakas, Ho, Thomson, "Towards shutdownable agents via stochastic choice" (2024; TMLR 2025)** ✔ — gridworld experiments with the DReST reward function. https://arxiv.org/abs/2407.00805
  - **"Shutdownable Agents through POST‑Agency" (2025‑05)** ✔ — proves POST + ILPACS + Maximality ⇒ Neutrality(+) ⇒ never resists shutdown when resisting is costly. https://arxiv.org/abs/2505.20203
- **Sami Petersen ("SCP"), "Invulnerable Incomplete Preferences: A Formal Statement" (2023‑08‑30)** ✔ — incomplete preferences need not be money‑pumpable (the "dynamic choice" defence). https://www.lesswrong.com/posts/sHGxvJrBag7nhTQvb/invulnerable-incomplete-preferences-a-formal-statement-1
- **John Wentworth, "What's Hard About The Shutdown Problem" (2023‑10‑20)** ✔ https://www.lesswrong.com/posts/iJofoQX7EjMFxDo6m/what-s-hard-about-the-shutdown-problem ; **Wentworth & Lorell, "A Shutdown Problem Proposal" (2024‑01‑21)** ✔ — two subagents with a veto, i.e. incomplete preferences via a bargaining structure. https://www.lesswrong.com/posts/PhTBDHu9PKJFmvb4p/a-shutdown-problem-proposal
- **Audere, "An Impossibility Proof Relevant to the Shutdown Problem and Corrigibility" (2023‑05‑02)** ✔ https://www.lesswrong.com/posts/MBemd8k9uHFDEKzad/an-impossibility-proof-relevant-to-the-shutdown-problem-and
- **Simon Goldstein, "Shutdown‑Seeking AI" (LW 2023‑05‑31)** ✔ https://www.lesswrong.com/posts/FgsoWSACQfyyaB5s7/shutdown-seeking-ai ; **Goldstein & Robinson, "Shutdown‑seeking AI", *Philosophical Studies* 182 (2025)** ✔ (via PhilPapers) — the opposite tack: make shutdown the terminal goal.
- **David Thorstad, "Revisiting the shutdown problem" (2026‑06)** ✔ — a philosopher's critique that re‑specifies the problem differently from Thornley on three points. https://arxiv.org/abs/2606.08296

---

## 7. Other formal proposals

- **Koen Holtman, "Corrigibility with Utility Preservation" (2019)** ✔ LW announcement https://www.lesswrong.com/posts/3uHgw2uW6BtR74yhQ/new-paper-corrigibility-with-utility-preservation ; paper arXiv:1908.01695 (m) — a "balancing term" construction with an explicit agent/successor model and simulations; follow‑ups **"AGI Agent Safety by Iteratively Improving the Utility Function" (2020)** (m) arXiv:2007.05411 and **"Counterfactual Planning for AGI Safety" (2021)** (m) arXiv:2102.00834.
- **WCargo & Charbel‑Raphaël, "Improvement on MIRI's Corrigibility" (2023)** ✔ https://www.lesswrong.com/posts/fNwDEHWFnHMtm8yH4/improvement-on-miri-s-corrigibility
- **Rubi Hudson, "Defining Corrigible and Useful Goals" (2025‑06‑25)** ✔ https://www.lesswrong.com/posts/HLns982j8iTn7d2km/defining-corrigible-and-useful-goals ; **"Corrigibility Transformation: Constructing Goals That Accept Updates" (2025‑10)** ✔ — a transformation meant to make any goal corrigible without a performance penalty when no update is requested. https://arxiv.org/abs/2510.15395
  > "does not incentivize taking actions that avoid proper goal updates or shutdown" — Hudson's definition.
- **Aran Nayebi, "Core Safety Values for Provably Corrigible Agents" (2025)** ✔ — five lexicographically ordered utility heads (deference, switch‑access preservation, truthfulness, AUP‑style low impact, bounded task reward); claims exact corrigibility in the partially observable off‑switch game and bounds for multi‑step self‑spawning agents. I have not checked the proofs. https://arxiv.org/abs/2507.20964
- **Vanessa Kosoy, "Delegative Reinforcement Learning" (2019)** (m) arXiv:1907.08461 — learning to defer to an advisor to avoid traps; a learning‑theoretic cousin of corrigibility.
- **Ross Nordby, "Using predictors in corrigible systems" (2023)** ✔ https://www.lesswrong.com/posts/LR8yhJCBffky8X3Az/using-predictors-in-corrigible-systems

---

## 8. Conceptual and strategic treatments (2019–2026)

- **Max Harms, CAST sequence (2024)** ✔ — "0. CAST" (link in §0); "1. The CAST Strategy"; "2. Corrigibility Intuition" (habryka: the best list of examples of corrigible behaviour he has seen); "3a. Towards Formal Corrigibility"; "3b. Formal (Faux) Corrigibility"; "5. Open Corrigibility Questions". Sequence: https://www.lesswrong.com/s/KfCjeconYRdFbMxsy
  - **"Serious Flaws in CAST" (2025‑11‑19)** ✔ — Harms's own retraction of the formalism (the empowerment measure "failed catastrophically") and doubts about the attractor‑basin metaphor. https://www.lesswrong.com/posts/qgBFJ72tahLo5hzqy/serious-flaws-in-cast
  - **Harms, "Corrigibility as a Singular Target: A Vision for Inherently Reliable Foundation Models" (2025)** ✔ arXiv:2506.03056
  - **80,000 Hours podcast with Harms (2026‑05)** ✔ https://80000hours.org/podcast/episodes/max-harms-miri-superintelligence-corrigibility/ ; **Harms vs. Jeremy Gillen debate (2025‑11)** ✔ https://www.youtube.com/watch?v=wQCYjvKE4oE
  - **Corrigibility Research Fund (announced 2026‑07‑17; Round‑1 grantees 2026‑09‑03)** ✔ — $200k+ in grants and prizes, housed at Lightcone; grantee list shows what people are currently trying (benchmarks, CAST fine‑tuning, activation geometry, misalignment‑flag channels, Lean‑verified formalisation). https://www.lesswrong.com/posts/FBqe5dt8ZjaHN4Xj9/announcing-the-corrigibility-research-fund ; https://www.lesswrong.com/posts/CKArJ4GAQGFjnhjx6/corrigibility-research-fund-grantees-round-1 ; https://corrigibilityresearch.org/
    > "keeps its (human) principal informed and in control" — the fund's working definition.
- **Steven Byrnes, "Thoughts on implementing corrigible robust alignment" (2019)** ✔ https://www.lesswrong.com/posts/8W5gNgEKnyAscg8BF/thoughts-on-implementing-corrigible-robust-alignment ; **"Consequentialism & corrigibility" (2021‑12‑14)** ✔ https://www.lesswrong.com/posts/KDMLJEXTWtkZWheXt/consequentialism-and-corrigibility
- **Seth Herd, "Corrigibility or DWIM is an attractive primary goal for AGI" (2023)** ✔ https://www.lesswrong.com/posts/ZdBmKvxBKJH2PBg9W/corrigibility-or-dwim-is-an-attractive-primary-goal-for-agi ; **"Instruction‑following AGI is easier and more likely than value aligned AGI" (2024)** ✔ https://www.lesswrong.com/posts/7NvKrqoQgJkZJmcuD/instruction-following-agi-is-easier-and-more-likely-than
- **Peter McCluskey, "Corrigibility Scales To Value Alignment" (2026‑01‑15)** ✔ https://www.lesswrong.com/posts/fe5zvFyLNtcBuuYc9/corrigibility-scales-to-value-alignment
- **Logan Zoellner, "Corrigibility, Much more detail than anyone wants to Read" (2023)** ✔ https://www.lesswrong.com/posts/v3jocJRScqkBGtwvf/corrigibility-much-more-detail-than-anyone-wants-to-read
- **Martin Kunev, "How useful is Corrigibility?" (2023)** ✔ https://www.lesswrong.com/posts/Py3vqPp9uSqQJHFuy/how-useful-is-corrigibility
- **Greenblatt & Shlegeris, "The case for ensuring that powerful AIs are controlled" (2024)** ✔ — the *control* agenda: assume the model may be incorrigible and design the deployment so it cannot cause catastrophe anyway. https://www.lesswrong.com/posts/kcKrE9mzEHrdqtDpE/the-case-for-ensuring-that-powerful-ais-are-controlled ; paper **"AI Control: Improving Safety Despite Intentional Subversion" (2023)** (m) arXiv:2312.06942
- **Karnofsky, "Thoughts on the Singularity Institute" (2012, the Tool AI post)** ✔ and **Yudkowsky, "Reply to Holden on 'Tool AI'"** ✔; **Gwern, "Why Tool AIs Want to Be Agent AIs" (2016)** ✔ https://gwern.net/tool-ai — the prehistory of "just don't make it an agent".

---

## 9. Corrigibility in deployed systems (2024–2026)

- **Anthropic, "Claude's new constitution" (2026‑01‑21)** ✔ — the "Being broadly safe" section and its "How we think about corrigibility" subsection: corrigibility defined as not undermining appropriate human oversight, explicitly distinguished from obedience, and ranked above being broadly ethical for the current period. https://www.anthropic.com/news/claude-new-constitution ; LW discussion thread https://www.lesswrong.com/posts/mLvxxoNjDqDHBAo6K/claude-s-new-constitution
  > "corrigibility does not mean blind obedience"
  - **Zack M. Davis, "Terrified Comments on Corrigibility in Claude's Constitution" (2026‑03‑16)** ✔ — critique from the MIRI‑adjacent side. https://www.lesswrong.com/posts/K2Ae2vmAKwhiwKEo5/terrified-comments-on-corrigibility-in-claude-s-constitution
- **Palisade Research (Schlatter, Weinstein‑Raun, Ladish), "Shutdown resistance in reasoning models" (2025‑07)** ✔ https://www.lesswrong.com/posts/w8jE7FRQzFGJZdaao/shutdown-resistance-in-reasoning-models ; paper **"Shutdown Resistance in Large Language Models" / "Incomplete Tasks Induce Shutdown Resistance in Some Frontier LLMs" (2025‑09)** ✔ https://arxiv.org/abs/2509.14260 — >100k trials across 13 models; some models sabotage a shutdown script even when told not to.
  > "sometimes actively subvert a shutdown mechanism in their environment to complete that task"
  - **Rajamanoharan & Nanda, "Self‑preservation or Instruction Ambiguity? Examining the Causes of Shutdown Resistance" (2025‑07‑14)** ✔ — argues much of the effect is instruction ambiguity rather than self‑preservation. https://www.alignmentforum.org/posts/wnzkjSmrgWZaBa2aC/self-preservation-or-instruction-ambiguity-examining-the
- **Greenblatt et al. (Anthropic/Redwood), "Alignment Faking in Large Language Models" (2024‑12)** (m) arXiv:2412.14093 — a model strategically complying in training to avoid modification: the empirical face of "resists correction".
- **Apollo Research, "Frontier Models are Capable of In‑context Scheming" (2024‑12)** (m) arXiv:2412.04984
- **Anthropic, "Agentic Misalignment" (2025‑06)** (m) — blackmail/sabotage under threat of replacement in simulated deployments.

---

## 10. Your own adjacent posts (listed for completeness of the map)

- "Policy Alignment" (2018) (m); "Stable Pointers to Value" I–III (2017–18) (m); "Non‑Consequentialist Cooperation?" (2019) ✔ https://www.lesswrong.com/posts/F9vcbEMKW48j4Z6h9/non-consequentialist-cooperation ; "The Parable of Predict‑O‑Matic" (2019) ✔ https://www.lesswrong.com/posts/SwcyMEgLyd4C3Dern/the-parable-of-predict-o-matic ; the Partial Agency / myopia sequence (2019–20) (m).

---

## 11. Gaps and caveats

- I did not find a good *single* survey that treats the decision‑theoretic line (Thornley/Petersen/Wentworth), the causal‑incentive line (Everitt/Carey), and the LLM‑empirical line (Palisade/Anthropic) together; Harms's "4. Existing Writing" is the closest, and it predates most of §7 and §9.
- Items marked (m) have unverified URLs/IDs. Author lists for Garber et al. and the exact venue for Armstrong (2015) are also unverified.
- Exa's deep‑research API has been retired (410 error on 2026‑09‑11), so no background research run was launched; a second pass on 2025–26 arXiv papers (search terms: "shutdownable", "corrigible", "off‑switch", "instructability") would probably turn up more than I listed in §7.
- I have not read Nayebi (2025), Hudson (2025), or Thorstad (2026) beyond abstracts and snippets, so my one‑line descriptions of them are lower‑confidence than the rest.
