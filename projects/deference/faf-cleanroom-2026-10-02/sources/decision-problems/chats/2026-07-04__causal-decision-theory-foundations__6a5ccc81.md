---
title: "Causal decision theory foundations"
uuid: 6a5ccc81-f031-48d4-9c6f-532534e3727f
date: 2026-07-04
source: claude.ai
path: ai-safety/decision-theory
messages: 4
keywords: ["causal decision theory", "decision theory foundations", "CDT formalisms", "Pearl causality", "logic of conditionals", "suppositional decision theory", "Gallow", "Joyce", "Lewis", "act-state independence"]
classification_confidence: high
sensitive: false
---

# Causal decision theory foundations

**Summary.** User brings comprehensive research on causal decision theory formalisms and concerns about the relationship between Pearl's causality and academic CDT consensus. Claude serves as a tutor, proposing and then executing a structured 6-stage lesson plan on CDT foundations: Savage's framework, Jeffrey-Bolker algebras, the suppositional decision-theoretic frame, Gallow's spectrum of CDT formulations, Pearl vs philosophical CDT divergences, and handling probability-zero acts. The conversation demonstrates engaged collaborative learning on formal decision-theoretic foundations.

**Where to look:**
- 1: User uploads deep research on CDT formalisms, notes concerns about non-equivalent axiomatizations and Pearl-vs-CDT divide, requests tutoring
- 2: Claude proposes 6-stage lesson plan covering Savage, Jeffrey-Bolker, suppositional DT, Gallow's spectrum, Pearl vs CDT, and probability-zero acts
- 3: User accepts lesson plan, waives detailed Savage axiom work due to familiarity
- 4: Claude begins Stage 1 on Savage framework, explaining act-state independence and why EDT cannot be formulated within it

---

## [1] Human — 2026-07-04T17:40:25.080783Z

*[attachment: txt]*

````


/

What formalisms are there for causal decision theory? By default I would look at Foundations of Causal Decision Theory, but I haven't yet. However, Daniel Herrmann's thesis mentions that FCDT doesn't use "genuine" counterfactuals (in the specific sense of counterfactuals for probability-zero events), but the same author does use "genuine" counterfactuals elsewhere; this does make me worry that FCDT might be missing some important things. I've heard that although CDT advocates tend to talk as if there is one unified CDT, in fact there are like 5 non-equivalent axiomatizations which don't have well-understood relationships to each other. Separately, I've heard that there is a growing consensus within academic CDT that Pearl's causality is not the same thing -- this is concerning to me, since I've imagined "CDT" as basically Pearl's causal networks plus the idea that you need to cut the links to parents of the action node when counterfacting!





Synthesized multiple CDT formalisms and Pearl's divergence from academic consensus

Synthesized multiple CDT formalisms and Pearl's divergence from academic consensus

Here's a map of the territory, grounded in what I found. I'll keep each piece compact; tell me where to dig deeper.



The classical formulations. The standard list is roughly: Stalnaker / Gibbard–Harper (expected utility via probabilities of subjunctive conditionals, 

U

(

A

)

=

∑

O

P

(

A

□

 ⁣

 ⁣

→

O

)

V

(

O

)

U(A)=∑ 

O

​

 P(A□→O)V(O)), Lewis 1981 (expectation over a partition of "dependency hypotheses"), Skyrms 1980/1982 ("K-expectation" over factors outside the agent's influence), Sobel (counterfactual chances), and Joyce 1999 (imaging-based conditional expected utility with a representation theorem). So "about 5" is accurate. But "relationships not well-understood" is now outdated: Gallow's 2024 Pacific Philosophical Quarterly paper "Counterfactual Decision Theory Is Causal Decision Theory" is cited by people in this literature as the overview of the formulations and their interrelations. Gallow organizes them on a single axis — how much counterfactual determinacy each assumes: 

Stanford Encyclopedia of Philosophy



"Stalnaker and Gibbard & Harper—assume that is always determinate which outcome would result... Lewis and Skyrms assume only that it is determinate what the chance of any outcome would be... Sobel and Joyce... allow that even the counterfactual chances could be indeterminate." — Gallow, philarchive draft



Lewis himself argued in 1981 that the situation "is not the chaos of disparate approaches that it may seem" (Lewis, "Causal Decision Theory"), and the SEP entry says the versions make equivalent recommendations when their background assumptions are met, pointing to Bales (2016) for comparisons in cases where the assumptions fail. So: equivalence is conditional on substantive assumptions about determinacy, and there's live disagreement (Hedden's 2023 Mind paper "Counterfactual Decision Theory" argues causation and counterfactuals come apart under overdetermination, constitution, and determinism, and that the counterfactual version is the correct one; Gallow replies that all the founders were already counterfactual decision theorists). 

Stanford Encyclopedia of Philosophy



Pearl vs. academic CDT. Your picture — causal networks plus cutting links into the act node — is essentially the Meek–Glymour (1994) proposal, endorsed by Pearl and Hitchcock. The philosophers' complaint is not that this is unrelated to CDT, but that it isn't equivalent to it without extra assumptions, in two specific ways. First, 

P

(

y

∣

d

o

(

x

)

)

P(y∣do(x)) presupposes a single known causal model; with uncertainty over causal structure you need a mixture over models, which is just the Lewis–Skyrms K-partition with causal models playing the role of dependency hypotheses — this is Reuben Stern's "interventionist decision theory" (Synthese 2017). Wolfgang Schwarz's analysis is blunt: after fixing the problems with Meek–Glymour, you arrive back at roughly Lewis 1981 / Skyrms 1982, and the concept of an intervention turns out to be both problematic and redundant in this context (blog post). Second, the do-operator treats your act as an exogenous miracle, but real agents' choices are caused; Stern's "An Interventionist's Guide to Exotic Choice" (Mind 2021) shows the Causal Markov Condition then admits spurious act–noneffect correlations, and notes that 

P

(

y

∣

d

o

(

x

)

)

P(y∣do(x)) "is not a true conditional" probability in the agent's credence space. This second problem should look familiar — it's the embedded-agency objection, arrived at independently. Note that Pearl himself does not concede any of this; his 2021 technical report claims SCMs settled the debate. So "consensus" overstates it; "substantial philosophical agreement that bare interventionism ≠ CDT, contested by Pearl's camp" is more accurate. 

Stanford Encyclopedia of Philosophy



On Herrmann and FCDT. His dissertation is "Naturalizing Decision Theory" (UC Irvine 2023, advisor Huttegger); I couldn't access the body to verify the specific remark about FCDT, so I can't confirm the framing, but the claim is plausible: Joyce builds CDT on imaging within a Bolker-style representation-theorem framework, and Joyce (2002) defends agents having nonzero credences in their own acts — so counterfactuals at probability-zero events (the full-conditional-probability / Popper-function apparatus) are simply not the machinery FCDT runs on. Whether that's a defect depends on whether you think probability-zero acts are a case the theory must handle; that's exactly the act-credences debate (Spohn and Levi say acts shouldn't get credences at all). I'd say this doesn't make FCDT "missing something" for your purposes so much as scoped differently — its contribution is the representation theorem and the unification of EDT and CDT as two supposition operations (conditioning vs. imaging) within one conditional-expected-utility framework, which it states explicitly as its goal in the introduction.



One more thing, separate from your question: Herrmann & Rothfus have a 2025 Theory and Decision paper, "Deference and decision", proving that no decision theory agreeing with EDT and CDT wherever they agree can both (a) never use the value of evidence-inconsistent events and (b) defer to what a better-informed version of yourself would do — an impossibility result about deference principles in decision theory. Given your project files, you may want this on your reading list independently of the CDT question. 

Springer



Suggested reading order, given your goals: Gallow 2024 first (it's the relationship map you've heard doesn't exist), then Stern 2021 and Schwarz's post for the Pearl question, with Joyce's FCDT after — reading it for the representation-theorem framework rather than for a theory of counterfactuals. Want me to go deeper on any single formulation (e.g., work through Lewis's dependency-hypothesis formulation and exactly when it coincides with Gibbard–Harper), or on the exotic-choice argument?



Oh, go ahead and do a proper Deep Research. I'm specifically interested in settings which make it possible to compare CDT and EDT; I've been told that Savage's theory is basically CDT, but does not have a structure that allows EDT to be formulated for comparison. Jeffrey-Bolker is basically EDT, but in contrast (so I've heard) it is possible to compare CDT and EDT in that setting (annotated with extra causal structure, I presume). I'm also quite curious about the thread I mentioned contrasting Pearl's causality with CDT notions of causality.



The request is clear enough to launch directly: you want the formal settings in which CDT and EDT can both be formulated and compared (Savage as implicitly-causal with no room for EDT, Jeffrey–Bolker as evidential but augmentable with causal structure, Joyce's unification, suppositional frameworks), plus the Pearl-vs-philosophical-CDT thread in depth. Off to do the research.





CDT and EDT formal frameworks



Research complete

•

205 sources

•

10m 4s

Your report on formal frameworks for CDT and EDT, and the Pearl-vs-CDT causality question, is ready. It verifies your three heard claims (with qualifications), maps Savage, Jeffrey–Bolker, Gibbard–Harper/Stalnaker, Lewis/Skyrms K-partitions, Sobel/Joyce imaging, causal Bayes nets/SCMs, Bradley's multidimensional worlds, and Elga's suppositional DT in a side-by-side comparison, and traces the Meek–Glymour/Pearl interventionist reading against the Lewis–Skyrms counterfactual tradition through Stern, Schwarz, Hedden, Gallow, Briggs, Fisher, and Zhang et al. The report includes a unifying suppositional-DT frame, Gallow's counterfactual-determinacy spectrum, a detailed framework comparison table, recommendations on which frame to adopt and how to handle probability-zero acts, and caveats noting that the "Pearl ≠ CDT causality" view is a live dispute rather than a settled consensus.





Formal Frameworks for EDT and CDT, and the Pearl-versus-CDT Causality Debate

Document 





Fable 5 is the most capable model and draws down usage much faster than Opus 4.8













Claude is AI and can make mistakes. Please double-check responses.

Formal Frameworks for CDT and EDT, and the Pearl-vs-CDT Causality Question

TL;DR

The user's first two heard claims are essentially correct but need qualification: Savage's states/acts/consequences architecture builds in act–state independence (via the Sure-Thing Principle, which — per the SEP Decision Theory entry — "is plausible only if the modelled acts are probabilistically independent of the states"), so the EDT/CDT contrast cannot even be posed there; Jeffrey–Bolker is the natural home of EDT but is a framework (a single probability–desirability space over propositions) into which CDT can be embedded by adding a supposition operator (imaging) or a privileged K-partition of dependency hypotheses — Joyce (1999) and Lewis (1981) do exactly this.

The cleanest unifying frame is suppositional decision theory: the value of an option A is its expected value under a supposition function P^A with P^A(A)=1; EDT = conditioning (P^A = P(·|A)), counterfactual CDT = counterfactual supposition / imaging, K-partition CDT = imaging relative to a dependency-hypothesis partition. Causal Bayes nets / SCMs realise this concretely as P(y|do(x)) vs P(y|x), but several authors (Schwarz, Stern, Hedden, Fisher, Zhang et al.) argue Pearl's interventionist causality is not the same as CDT's causality.

On Thread 2: there is a genuine, live dispute, not a settled "consensus", but the weight of recent academic philosophy holds that Pearl-style interventionism is at best one implementation of CDT and is inadequate or redundant as a foundation. CDT is most defensibly grounded in counterfactual/causal dependence (Lewis–Skyrms dependency hypotheses), which interventionist do(·) only approximates and sometimes gets wrong (exotic choice, uncertainty over causal structure, no-error-term cases). Pearl himself maintains that "Causal inference research in the past 3 decades has settled this debate by defining Px(y) in terms of Structural Causal Models" (R-512, 2021); almost no academic decision theorist accepts that strong claim.

Key Findings

Verification of the three heard claims

"Savage ≈ CDT, and EDT cannot be formulated there." Substantially correct. Savage's acts are functions from states to consequences; the Sure-Thing Principle (P2) is a theorem of the framework but, as the SEP Decision Theory entry stresses, P2 "is plausible only if the modelled acts are probabilistically independent of the states. In other words, this independence must be built into the decision model if it is to facilitate appropriate measures of belief and desire." Because states are defined to be act-independent objects of belief, there is no room within the canonical Savage apparatus to let P(state | act) differ from P(state), which is exactly the degree of freedom EDT-vs-CDT disagreement requires. So EDT cannot disagree with CDT inside orthodox Savage. The qualification: this is a feature of how the model is built, not a deep theorem — one can re-describe states as act-to-outcome functions (Gibbard–Harper's "states as functions") to dissolve Newcomb dominance, which is itself a CDT-flavoured move.

"Jeffrey–Bolker ≈ EDT but CDT can be formulated in it." Correct, and this is the heart of Joyce (1999). Jeffrey–Bolker abolishes the act/state/outcome trichotomy: probability and desirability are defined over a single Boolean algebra of propositions, acts included. The default decision rule (maximise Jeffrey desirability) is EDT. CDT is obtained by replacing the conditioning operator with a causal/subjunctive supposition operator — Joyce writes P(O\A) (backslash, subjunctive) in place of P(O/A) (slash, evidential). Lewis (1981) does the embedding via a K-partition of dependency hypotheses inside Jeffrey's V-function; Joyce proves a single Bolker-style representation theorem covering both.

"Pearl's causality = CDT's causality, with link-cutting." This is the claim most in need of correction. It is the Meek–Glymour (1994)/Pearl/Hitchcock interventionist reading, but a substantial recent literature (Stern 2017/2021, Schwarz 2017, Fisher 2017, Briggs 2012, Zhang–Lam–De Clercq 2013, Hedden 2023) argues that interventionist do(·)-counterfactuals diverge from the Lewisian causal-dependence counterfactuals that CDT actually needs. There is no settled consensus, but the interventionist-as-foundation view is now a minority position among philosophers of decision theory.

The unifying frame: suppositional decision theory

The most precise general setting is Adam Elga's reconstruction (drawing on Joyce 1999 ch. 6 and Lewis 1981). In Elga's "Confession of a Causal Decision Theorist" (Analysis 82(2):203–213, 2022), every theory in the family selects an option A maximising U(A) = E(v, P^A), the expectation of value v with respect to P^A, where the supposition function mapping P to P^A satisfies only that P^A is a probability function with P^A(A)=1. Elga writes:



"Evidential Decision Theory (Jeffrey 1965) is gotten by letting the supposition function be conditionalization: P^A(·) = P(·|A). Counterfactual causal decision theories (Gibbard and Harper 1978, Stalnaker 1981) are gotten by letting the supposition function be counterfactual supposition: P^A(·) = P(A □→ ·). K-partition causal decision theories are defined in terms of a privileged partition K of 'dependency hypotheses'… the supposition function is imaging relative to K: P^A(·) = Σ_{K∈K} P(K)P(·|AK)."



Elga's impossibility result (Bet + Two-box + Suppositional are jointly inconsistent, via "Betting on the laws" and "Newcomb on the past") shows the whole family fails to satisfy two independently attractive desiderata, which bears directly on the probability-zero/genuine-counterfactual issue below.



Gallow's spectrum of CDT formulations (degree of counterfactual determinacy)

Gallow (2024) maps all the "founding fathers" onto one axis — how much they take to be counterfactually determinate — and proves they coincide under added determinacy assumptions. He states: "the differences between causal decision theories concern how much they take to be counterfactually determinate. The earliest and simplest theories—from Stalnaker and Gibbard & Harper—assume that is always determinate which outcome would result… Lewis and Skyrms assume less… only that it is determinate what the chance of any outcome would be… Sobel and Joyce assume even less." From most to least determinacy:



Stalnaker (1981); Gibbard & Harper (1978) — Counterfactual Determinacy: for every act A and world W there is an outcome O with A □→ O true at W. Maximise U₁(A) = Σ_O P(A □→ O)·V(O).

Lewis (1981); Skyrms (1980) — Counterfactual Chance Determinacy: determinate what the chance of each outcome would be. Maximise U₂(A) = Σ_K P(K)·V(AK), K a dependency hypothesis (Lewis: a conjunction of probabilistic full patterns; Skyrms: maximally specific specification of factors outside the agent's influence).

Sobel (1994); Joyce (1999) — Counterfactual Chance Indeterminacy + primitive imaging: U₃(A) = Σ_W P^A(W)·V(W), P^A the causal probability/imaging function with P^A(A)=1.

These nest: "U₃ is a generalisation of U₂, just as U₂ was a generalisation of U₁," collapsing onto each other under counterfactual determinism plus value-level act–state outcomes (Gallow's Appendix Propositions 1–4 and Corollaries). Gallow's thesis: "counterfactual decision theory is not a competitor to, but rather a version of, causal decision theory—the most popular version by far." He argues the theories are called "causal" not because they track token causation (effects) but causal influence/control — "while you're responsible for your effects, you have control over what you affect" — and that "causal" was retained as a big-tent label "to accommodate reasonable disagreement about how to analyse causal influence."



Thread 2: Pearl vs CDT causality — the dialectic

Origin (interventionist CDT). Meek & Glymour (1994) "Conditioning and Intervening" propose that EDT and CDT use the same Jeffrey formula but disagree over whether the act is conditioned on as an observation (P(y|x), EDT) or as an intervention (P(y|do(x)), CDT). Endorsed by Pearl (Causality, 2009 ch.4) and Hitchcock (2016, Synthese), who extends it to "exotic" cases (crystal balls, time travellers).

Stern (2017, Synthese; 2021, Mind). Argues interventionist CDT inherits the expressive power of causal models but must be reconstructed as a Lewisian K-partition theory: "Lewis's causal decision theory can be rendered applicable to small world decisions if one analyzes his dependency hypotheses as causal hypotheses that depend on the interventionist causal modeling framework for their semantics", and this Lewisian-interventionist variant is preferable to do(·)-conditionalisation because it "captures the causal decision theorist's conviction that any correlation between what the agent does and cannot cause should be irrelevant to the agent's choice." His 2021 "exotic choice" cases show that when the agent has evidence about her own choice's outcome, the interventionist must adopt "an alternative Ramseyan conception" of choice and update on the intervention rather than the foreknown evidence. 

Springer

Semantic Scholar

Schwarz (2017, "Interventionist decision theory without interventions"). Three problems: (i) no guarantee an intervention/error term exists for the act ("An adequate decision theory should not presuppose that the relevant agent has libertarian free will"); (ii) where error terms exist, conditioning on do(B) may amount to conditioning on uncontrolled noise (random electromagnetic fluctuations) that are "not interventions or doings on part of the agent in any ordinary sense"; (iii) Stern's point that under uncertainty over causal structure, P(O | do(A)) is not a conditional probability in the agent's credence space — his H1/H2 example yields "Cr(O=1) = .5 [;] Cr(O=1 / I=1) = .9 * .9 + .1 * .1 = .82… although the agent assigns credence 1 to [a] causal hypothesis on which I and O are probabilistically independent, the two variables are not independent in her beliefs… But this means to act on a spurious correlation." Conclusion: "the supposedly central concept of an intervention… is not only problematic in this context, but also redundant"; fixing it returns us to Lewis (1981)/Skyrms (1982) with causal models as dependency hypotheses. 

umsu

umsu

Hedden (2023, Mind) vs Gallow (2024, PPQ). Hedden: causation and counterfactual dependence come apart in overdetermination (action causes good outcome with no counterfactual dependence), constitution (action constitutes rather than causes the good), and determinism (laws/past counterfactually but not causally depend on the act); "counterfactual decision theory" gives the right verdicts. Gallow: these are not a rival; properly read, the founding fathers' theories are counterfactual, and Hedden's cases are handled because outcomes are act–state conjunctions ("Causal decision theories don't calculate utility with the values of states alone… outcomes are act-state conjunctions. So the value of the act itself will be included" — constitution), CDT tracks influence not token effects (overdetermination), and impossible act–hypothesis conjunctions have undefined value so dominance fails ("BQ is metaphysically impossible. So V(BQ) is undefined" — determinism). 

PhilArchive

PhilPapers

Pearl's interventionist counterfactuals ≠ Lewisian counterfactuals. Briggs (2012) shows the extended causal-modeling language makes "modus ponens… invalid, and classical logical equivalents cannot be freely substituted in the antecedents of conditionals" — "unlike any logic of Lewis's." Fisher (2017) shows "strictly-interventionistic" semantics (forcing antecedent variables independent of their parents) cannot evaluate a class of (backtracking) causal counterfactuals; "causal counterfactuals are not interventionist counterfactuals." Zhang, Lam & De Clercq (2013) show Pearl's "reversibility" axiom "states a kind of irreversibility: counterfactual dependence (in David Lewis's sense) between two distinct events is irreversible," ruling out only mutual, not cyclic, dependence — "Pearl's logic is either too weak or too strong." Halpern (2000, 2013) and Galles & Pearl (1998) give the axiomatisations relating structural-equation counterfactuals to Stalnaker–Lewis logics.

Pearl's own position. In R-512 "Causation and Decision Theory" Pearl writes that Bayesian conditioning P_x(y)=P(y|x) "is inappropriate for serving in Eq. (1), for it leads to paradoxical results of several kinds… patients would avoid going to the doctor to reduce the probability that one is seriously ill; barometers would be manipulated to reduce the chance of storms," and that "Causal inference research in the past 3 decades has settled this debate by defining Px(y) in terms of Structural Causal Models." He argues SCMs give imaging a "decision-theoretic justification" and avoid Lewis's metaphysical "similarity," which "may differ from person to person and, thus, could not explain the uniformity with which people interpret causal utterances."

Details

1. Savage's framework and why EDT cannot be posed in it

Savage (1954): a decision problem is ⟨S, X, F, ⪯⟩ with states S, consequences X, acts F = X^S (functions from states to consequences), and a preference order ⪯ over acts. The representation theorem derives a (finitely additive) probability over S and a utility over X with f ⪯ g iff Σ_s p(s)u(f(s)) ≤ Σ_s p(s)u(g(s)). Crucially the probability is over states only, and states are by construction objects of belief whose probabilities do not depend on which act is chosen. The Sure-Thing Principle (P2) — that preference is unaffected by outcomes in states where two acts agree — is, as Titelbaum notes, "a theorem of Savage's decision theory… also therefore a theorem of Jeffrey's decision theory for cases in which acts and states are independent." The SEP Decision Theory article states the foundational point bluntly: P2 "is plausible only if the modelled acts are probabilistically independent of the states. In other words, this independence must be built into the decision model if it is to facilitate appropriate measures of belief and desire." Because act–state independence is presupposed, Newcomb-type act–state correlation is inexpressible; EDT (which is exactly the theory that takes P(state|act) ≠ P(state) seriously) has no foothold. Edi Karni's analysis adds that even Savage's state-independence of utility "is not implied by the postulates, it has no choice manifestation, and its validity is not subject to refutation in the context of Savage's analytical framework" — i.e. the independence is a modeling convention, not something the formalism can test.



The standard escape (Gibbard–Harper 1978; Luce–Raiffa) is to redescribe states as functions from acts to outcomes, so that "a 'state' whose occurrence partly depends on the decision-maker's act is not a state" and Newcomb's problem is rephrased with (at least) four states; in such a formulation "the dominance argument breaks down." But this already imports causal structure, confirming that the bare Savage frame cannot host the comparison.



2. Jeffrey–Bolker as EDT and the embedding of CDT

Jeffrey's Logic of Decision (1965) jettisons the trichotomy; desirability V and probability P live on one algebra of propositions. The default rule, maximise V(A) = Σ_O P(O|A)u(O∧A) ("news value"), is EDT. Bolker's representation theorem underwrites it but with two well-known costs (SEP Decision Theory): (a) partition invariance is a virtue Jeffrey's V uniquely has; (b) non-uniqueness — "it is neither guaranteed that there will be just one probability function that represents her beliefs nor that the desirability function… will be unique up to a positive linear transformation"; indeed "the same preference ordering satisfying all these axioms could be represented as maximising desirability relative to two probability functions that do not even agree on how to order propositions according to their probability." Joyce regards this non-uniqueness as correct (Jeffrey "gets things exactly right… one should not expect that reasonable conditions imposed on a person's preferences would suffice to determine a unique probability function… It is only by imposing overly strong conditions, as Savage does, that we can achieve this") but shows in FCDT that supplementing the Bolker–Jeffrey axioms with comparative-probability axioms restores uniqueness ("I remove the single outstanding problem with Bolker's theorem by reformulating it in a way which yields a unique probability and utility representation… I make use of axioms which govern not only preference but comparative probability"). 

Stanford Encyclopedia of Philosophy



CDT enters by changing the supposition operator. Joyce's notation: evidential P(O/A) (Bayesian conditioning) vs causal P(O\A), "the degree of credence in O on the subjunctive supposition that A," cashed out via Lewis 1976 imaging / general imaging (FCDT pp. 161–180). Lewis (1981) embeds CDT directly in Jeffrey's V by restricting attention to a partition K of dependency hypotheses and computing U(A) = Σ_K C(K)V(AK), where a dependency hypothesis is "a maximally specific proposition about how the things [the agent] cares about do and do not depend causally on his present actions." Skyrms (1980, 1982) uses "causal propensities" / "the factors outside our influence at the time of decision which are causally relevant to the outcome of our actions"; Lewis reads these as equivalent to his dependency hypotheses under a broad interpretation. This is precisely "Jeffrey–Bolker plus causal structure."



3. Joyce's representation theorem and its limits

Joyce (FCDT ch. 6–7) proves a Bolker-styled representation theorem for an abstract conditional decision theory whose two primitives are "probability under a supposition and preference under a supposition," with both EDT (indicative/matter-of-fact supposition) and CDT (subjunctive supposition) as special cases. Joyce calls it "the most widely applicable and intuitively satisfying representation result yet attained," noting "No truly general and satisfactory representation theorem (along the lines of Bolker's evidential representation theorem) had been proven for causal decision theory" before it. Limitations and criticisms:



It requires richness/structure axioms (a completeness axiom and an atomlessness/non-atomicity condition) plus, for uniqueness, comparative-probability axioms beyond preference — so it is not purely behaviouristic.

The general supposition operator must satisfy "centered conditional" constraints (Conditional Contradiction, Harmony, Conditional Excluded Middle; FCDT p. 168), which build in CEM and so inherit the triviality-result tensions around subjunctive conditional probability.

Probability-zero acts. Joyce, like the suppositional framework generally, faces the P(A)=0 case; Elga explicitly brackets "some technical messiness associated with the case of P(A) = 0, orthogonal to present concerns." Joyce's machinery uses Rényi–Popper measures (FCDT §6.4) — primitive conditional probabilities — to handle conditioning on null events and the problem of old evidence, which is one of the cleaner ways CDT can supply "genuine counterfactuals" for null acts.

4. The act-credence / DCOP debate (cross-cutting)

Whether agents may assign credences to their own acts (needed for Jeffrey-style EDT and for any account treating acts as ordinary propositions) is contested. Spohn (1977) and Levi (1989, "Deliberation Crowds Out Prediction", DCOP) argue act credences are incoherent because the betting interpretation collapses on action-events; in Levi's slogan, "to be an agent crowds out being a predictor." Joyce (2002, "Levi on Causal Decision Theory and the Possibility of Predicting One's Own Actions") and Rabinowicz (2002), Hájek (2016), and Ahmed (2014) reject DCOP; Joyce's "Evidential Autonomy Thesis" holds "A deliberating agent who regards herself as free need not proportion her beliefs about her own acts to the antecedent evidence that she has for thinking that she will perform them." Liu & Price (2018, 2019) argue the dispute is largely terminological/model-relative (DCOP holds in Ramsey's operationalist model, fails in trivially extended models) and that Joyce's EAT "is effectively DCOP, in different terminological clothing," both resting on first-person transparency. This matters because CDT's interventionist reading often presupposes the act is treated as exogenous (free), which is the free-will-adjacent assumption Schwarz flags.



5. Causal Bayes nets / SCMs as the cleanest comparison setting — and its subtleties

In a causal Bayes net, EDT computes P(o|a) (conditioning, "see"), CDT computes P(o|do(a)) (intervening, "do"), the latter via graph surgery cutting incoming edges to the action node. This is the setting where the formal contrast is sharpest. But four subtleties undercut treating it as the foundation of CDT:



do(·) is not a credence-space conditional. As Schwarz shows, under uncertainty over which causal model is correct, the agent's credence Cr(O|do(A)) mixes over models and can become sensitive to spurious act–model correlations (his H1/H2 example: Cr(O=1)=.5 but Cr(O=1|I=1)=.82 even though every model treats O,I as independent). do(·) lives in the objective model; the agent's decision-relevant quantity lives in her credence space. 

umsu

Mixtures over causal models are required (Stern's interventionist DT, Schwarz's "doubly causal" reconstruction): EU(A) = Σ_K Cr(K) Σ_O Cr(O|do(A)∧K)V(O). Once you do this, the dependency-hypothesis K-partition is doing the work and do(·) is arguably redundant ("the revised version of Stern's account is basically the decision theory of Lewis and Skyrms. The only difference is that dependency hypotheses are spelled out as causal models").

Acts as interventions vs caused events. When the act has no error term / is fully determined (a robot, or a determined agent), there is no do(·) event distinct from the act, so interventionist CDT is undefined; yet decisions still arise.

Exotic choice (Stern 2021): with foreknowledge of one's act's outcome, the Causal Markov Condition can admit correlations between act and non-effects (predictors, agents whose acts are caused), and naive intervening gives wrong verdicts; the fix requires a Ramseyan reconception of choice (chance indifference/transparency).

6. Pearl's interventionist counterfactuals vs Lewisian counterfactuals (logic)

The formal-logic literature establishes concrete divergences:



Briggs (2012): in the extended causal-modeling language, "modus ponens is invalid, and classical logical equivalents cannot be freely substituted in the antecedents of conditionals" — so the logic is "unlike any logic of Lewis's." 

PhilPapers

Fisher (2017): "strictly-interventionistic" semantics (which require antecedent variables to be made independent of their parents) cannot adequately evaluate a class of (backtracking) causal counterfactuals; hence "causal counterfactuals are not interventionist counterfactuals." 

Academia.edu

Zhang, Lam & De Clercq (2013): Pearl's reversibility axiom "states a kind of irreversibility: counterfactual dependence (in David Lewis's sense) between two distinct events is irreversible," and rules out only mutual, not cyclic, dependence — "Pearl's logic is either too weak or too strong."

Halpern (2000, "Axiomatizing Causal Reasoning"; 2013, "From Causal Models to Counterfactual Structures") and Galles & Pearl (1998): axiomatise the structural-equation counterfactual and compare to Stalnaker–Lewis; structural counterfactuals are non-backtracking and validate principles Lewis's logic does not.

Backtracking / miracles: Pearl (2009 p.239) replaces Lewis's miracles with structural interventions; Gallow (2022, "Causal Counterfactuals without Miracles or Backtracking") offers a third route. These differences are decision-theoretically live because, as Elga's and Ahmed's determinism cases show, the verdict in "Betting on the laws"/"Newcomb on the past" depends on whether counterfactuals backtrack to the laws or the past. 

arxiv

7. AI-alignment / agent-foundations adjacent literature (secondary)

Everitt et al.'s Causal Influence Diagrams (Pearl's graphs + decision/utility nodes; "Agent Incentives: A Causal Perspective", AAAI 2021) operationalise do(·)-style reasoning for embedded agents and define instrumental control incentives, response incentives, value of information/control. The MIRI line (Yudkowsky & Soares 2017, "Functional Decision Theory") argues both EDT and CDT mishandle Newcomblike problems for embedded agents — EDT "cannot imagine breaking correlations between their action and their environment," whereas "CDT agents fail because they imagine breaking too many correlations" — motivating subjunctive dependence on the agent's decision function (a non-suppositional move). This bears on whether Pearl-style models capture decision-relevant causality for agents who are parts of the modelled world (the "exotic choice"/embedded-agency overlap), but it is downstream of, and less rigorous than, the academic philosophy debate.



Framework-by-framework comparison

Framework	Primitive objects	Where probabilities live	Where utilities live	Acts get credences?	EDT formulable?	CDT formulable?	Extra structure CDT needs	Prob-0 acts handled?	Representation theorem	Main criticisms

Savage (1954)	States, consequences, acts = functions S→X	Over states only (act-independent)	Over consequences	No (acts aren't in belief algebra)	No (act–state independence presupposed)	Implicitly (it is the act-independent EU rule)	— (already act-independent)	N/A	Yes, unique p and u (u up to affine)	State/utility independence is a non-testable convention (Karni); too idealised

Jeffrey–Bolker (1965)	Propositions (one algebra incl. acts)	Over all propositions	Desirability over all propositions	Yes	Yes (maximise V, "news value")	Yes — swap conditioning for subjunctive supposition / K-partition	Supposition operator (imaging) or K-partition	Via Rényi–Popper extension	Bolker's theorem (non-unique p,u)	Non-uniqueness; partition-invariance is a plus

Gibbard–Harper / Stalnaker (1978/1981)	Worlds + Stalnaker selection function; acts as propositions	Subjective P over counterfactuals A □→ O	V over outcomes	Yes	Yes (as EDT special case)	Yes — U₁ = Σ P(A □→ O)V(O)	Selection function; CEM/counterfactual determinacy	Selection semantics defined at null antecedents	Stalnaker letter to Lewis; Gibbard–Harper construction	Requires CEM; counterfactual determinacy too strong (Hedden)

Lewis (1981) K-partitions	Dependency hypotheses K (in Jeffrey V)	C over K	V(AK)	Yes	Yes	Yes — U₂ = Σ C(K)V(AK)	Privileged partition of dependency hypotheses	Inherits Jeffrey treatment	Uses Jeffrey/Bolker	Need a way to find the K-partition (Eells); circularity worry

Skyrms (1980,1982)	Causal propensities / factors outside influence	Causal propensity CP	V	Yes	Yes	Yes — K-expectation	Specification of admissible K's	—	No representation theorem (Eells's complaint)	Lacks rep. theorem; characterisation of K's contested

Sobel (1994) / Joyce (1999) imaging	Worlds + imaging function W^A	Causal probability P^A (image), P^A(A)=1	V over worlds/outcomes	Yes	Yes (P^A = conditioning)	Yes — U₃ = Σ P^A(W)V(W)	Imaging kernel (centered conditional)	Yes — Rényi–Popper / primitive conditional prob	Yes — Joyce's unified Bolker-style theorem	Needs richness + comparative-prob axioms; CEM-laden

Causal Bayes nets / SCMs (Meek–Glymour 1994, Pearl)	DAG + structural equations + chances	Objective chances in model; agent credence over models	V over outcomes	Depends (act = node, possibly exogenous)	Yes — P(o|a)	Yes — P(o|do(a)), graph surgery	Causal graph + do-operator; mixture over models if uncertain	do(·) ill-defined if no error term / P(act)=0	Pearl's vNM-style result (known structure)	do(·) not a credence conditional; redundant given K-partition (Schwarz); exotic choice (Stern)

Bradley (2017) multidimensional worlds	Sequences of states (actual + one per supposition); prospects	P over multidimensional worlds (modal uncertainty)	Desirability over prospects	Yes	Yes (evidential supposition)	Yes (counterfactual supposition dimension)	Extra "counterfact" dimensions per supposition	Yes (modal uncertainty representable)	Representation theorem for conditionals (Bradley 1999/2012)	Interpretive vagueness of prospects; atomlessness demanding

Suppositional DT (Elga 2022, general)	Options, value v, supposition function P^A	P and all P^A	v over worlds	Yes	Yes (P^A = P(·|A))	Yes (P^A = imaging/counterfactual)	Any supposition function with P^A(A)=1	Bracketed ("technical messiness")	Subsumes Joyce's	Impossibility result: Bet+Two-box+Suppositional inconsistent

Recommendations

Adopt the suppositional-DT frame (Joyce/Elga) as the canonical comparison setting, not Savage. State EDT and CDT as two choices of supposition function P^A on a single Jeffrey–Bolker algebra. This makes the minimal extra structure CDT needs explicit: an imaging kernel or a K-partition of dependency hypotheses. Use this when you need a representation theorem (Joyce ch. 7).

Use causal Bayes nets/SCMs for concreteness and computation, but do not treat do(·) as the definition of CDT's causal probability. Treat causal models as candidates for dependency hypotheses and mix over them (Stern/Schwarz): EU(A) = Σ_K Cr(K) Σ_O Cr(O|do(A)∧K)V(O). This is the position that survives Schwarz's three objections and Stern's exotic-choice cases.

For null/probability-zero acts and "genuine counterfactuals", reach for primitive conditional probabilities — Rényi–Popper functions (Joyce FCDT §6.4), full conditional probabilities, or a Stalnaker selection function defined at null antecedents; lexicographic probabilities are an alternative. Avoid frameworks that require P(A)>0 for all options if you must evaluate dominated/unchosen acts. The Herrmann–Rothfus (2025) "Deference and Decision" common counterfactual framework with "genuine counterfactuals" is the most recent attempt to formulate both EDT and CDT in one setting and is worth tracking for this purpose.

Correct the user's third belief explicitly: "CDT = Pearl + cut parent links" is the Meek–Glymour interventionist reading, defensible in well-behaved cases but (i) not what the founding texts say (they use counterfactual dependence), (ii) provably divergent in logic (Briggs, Fisher, Zhang et al.), and (iii) arguably redundant (Schwarz). Present it as one implementation, flagged as contested.

Benchmarks that would change these recommendations: if a representation theorem for an interventionist CDT that (a) handles uncertainty over causal structure without reducing to K-partitions and (b) handles exotic choice without a Ramseyan reconception were proven, the "do(·) is redundant" verdict would weaken. If Pearl-style structural counterfactuals were shown to coincide with the decision-relevant counterfactuals in all determinism cases (resolving the backtracking dispute), Hedden's and Ahmed's objections would lose force.

Caveats

"Growing consensus" is overstated. The accurate statement is: among philosophers working on the foundations of decision theory, the interventionist-as-foundation view (do-calculus = CDT) is now a minority and is under sustained, largely successful, critique — but Pearl and parts of the CS/AI community maintain that SCMs settled the matter. This is a live, camp-structured dispute, not a settled consensus. Camps: interventionist (Meek–Glymour, Pearl, Hitchcock, partly Stern); Lewis–Skyrms dependency-hypothesis / counterfactual (Lewis, Skyrms, Joyce, Gallow, Schwarz, Stern's reconstruction); counterfactual-not-causal (Hedden, with Collins, McNamara sympathetic); evidentialist (Ahmed, Eells historically, Price/Liu on deliberation).

Some sources are non-peer-reviewed (Schwarz's blog post; LessWrong/MIRI material). I have flagged these; Schwarz's arguments are widely cited and track Stern's published claims, but the blog itself is not peer-reviewed. The MIRI FDT material is secondary and less rigorous than the philosophy literature.

Pagination caveat on Gallow (2024): the freely accessible PhilArchive copy is paginated 1/30–30/30, not the journal's 115–156; quotes are verbatim from that draft, "forthcoming" but substantively matching the PPQ version.

Hedden vs Gallow is genuinely unresolved: whether the determinism cases refute CDT, or merely refute a particular theory of subjunctive supposition (Gallow's view, developed further in Gallow 2024 "Decision and Foreknowledge"), is contested; Elga's impossibility result suggests some attractive principle must be given up regardless.

Annotated bibliography (load-bearing passages, with links)

Joyce, J. (1999), The Foundations of Causal Decision Theory, CUP. The unification. "I prove a Bolker-styled representation result for an abstract conditional decision theory whose two primitives are probability under a supposition and preference under a supposition… it can be used as a common foundation for both causal decision theory and evidential decision theory." Free chapter 7 PDF: gwern.net/doc/statistics/decision/1999-joyce.pdf.

Elga, A. (2022), "Confession of a Causal Decision Theorist", Analysis 82(2):203–213. Defines suppositional DT (EDT = conditioning, GH/Stalnaker = counterfactual supposition, K-partition = imaging) and proves Bet+Two-box+Suppositional inconsistent. princeton.edu/~adame/papers/confession/.

Gallow, J.D. (2024), "Counterfactual Decision Theory Is Causal Decision Theory", PPQ 105(1):115–156. The determinacy spectrum (U₁/U₂/U₃) and reply to Hedden; "counterfactual decision theory is not a competitor to, but rather a version of, causal decision theory." philarchive.org/rec/GALCDT.

Hedden, B. (2023), "Counterfactual Decision Theory", Mind 132(527):730–761. Overdetermination/constitution/determinism cases. philarchive.org/rec/HEDCDT.

Lewis, D. (1981), "Causal Decision Theory", AJP 59(1):5–30. Dependency hypotheses; "maximally specific proposition about how the things [the agent] cares about do and do not depend causally on his present actions." 

philarchive

Meek, C. & Glymour, C. (1994), "Conditioning and Intervening", BJPS 45:1001–1021. Origin of interventionist CDT.

Hitchcock, C. (2016), "Conditioning, intervening, and decision", Synthese 193(4):1157–1176; (2013), "What is the 'cause' in causal decision theory?", Erkenntnis 78:129–146. Defends/extends interventionism to exotic cases; argues Lewisian causal dependence "is deserving of the epithet 'causal'."

Stern, R. (2017), "Interventionist decision theory", Synthese 194(10):4133–4153; (2021), "An Interventionist's Guide to Exotic Choice", Mind 130(518):537–566. Lewisian reconstruction; exotic choice; Ramseyan conception of choice.

Schwarz, W. (2017), "Interventionist decision theory without interventions" (blog, umsu.de/wo/2017/655). Three problems; do(·) "redundant"; returns to Lewis/Skyrms with causal models as dependency hypotheses. (Not peer-reviewed.)

Briggs, R. (2012), "Interventionist counterfactuals", Phil. Studies 160:139–166; Fisher, T. (2017), "Causal counterfactuals are not interventionist counterfactuals", Synthese 194:4935–4957; Zhang, Lam & De Clercq (2013), "A Peculiarity in Pearl's Logic of Interventionist Counterfactuals", J. Phil. Logic 42:783–794; Halpern (2000, 2013); Galles & Pearl (1998). Logic of interventionist vs Lewisian counterfactuals.

Pearl, J., R-512 "Causation and Decision Theory" (ftp.cs.ucla.edu/pub/stat_ser/r512.pdf); Causality (2009). "Causal inference research in the past 3 decades has settled this debate by defining Px(y) in terms of Structural Causal Models."

Spohn (1977); Levi (1989/2000); Joyce (2002); Rabinowicz (2002); Hájek (2016); Liu & Price (2018, 2019, "Ramsey and Joyce on Deliberation and Prediction", Synthese). Act-credence/DCOP debate.

Bradley, R. (2017), Decision Theory with a Human Face, CUP. Multidimensional possible-world semantics; both evidential and counterfactual suppositions defined; standard Bayesian EU recovered as a special case (ch. 9). personal.lse.ac.uk/bradleyr/.

Herrmann, D. & Rothfus, G. (2025), "Deference and Decision", Theory and Decision. Common counterfactual framework; impossibility result on Deference to the Foreseen vs the Seen — "no decision theory which agrees with [EDT] and [CDT] whenever they agree can satisfy both principles."

Everitt et al. (2021), "Agent Incentives: A Causal Perspective", AAAI; Yudkowsky & Soares (2017), "Functional Decision Theory" (arXiv 1710.05060). Agent-foundations adjacency (CIDs; FDT's subjunctive dependence on the decision function).














````
*[file: ]*

I'm trying to learn about the foundations of causal decision theory. I would appreciate it if you acted as a tutor and literature-review partner. I haven't properly worked through the material from the previous chat that I've pasted in here.

## [2] Claude — 2026-07-04T17:40:40.004465Z


<details><summary>thinking</summary>

I should structure this as a guided learning experience—break down the CDT foundations material into digestible chunks, outline a lesson plan, and get their input before diving in rather than overwhelming them with everything at once.

</details>

Given the material in that report, here's a proposed lesson plan. Tell me where you'd like to reorder, cut, or add:

1. **Savage's framework and why the EDT/CDT contrast can't be posed there.** States as act-independent objects of belief; the Sure-Thing Principle as the load-bearing assumption; the Gibbard–Harper "states as functions from acts to outcomes" redescription as an escape hatch that already smuggles in causal structure.
2. **Jeffrey–Bolker as the common arena.** One algebra of propositions, desirability as "news value", Bolker non-uniqueness, and why acts having credences matters here (touching the Spohn/Levi DCOP dispute if you want).
3. **The suppositional frame.** Elga/Joyce's picture: a decision theory is a choice of supposition function $P^A$ with $P^A(A)=1$. EDT = conditioning; CDT variants = various imaging/counterfactual operators. This is where the comparison you asked about becomes crisp.
4. **Gallow's determinacy spectrum.** How Stalnaker/Gibbard–Harper, Lewis/Skyrms, and Sobel/Joyce nest as $U_1 \subset U_2 \subset U_3$ under progressively weaker counterfactual-determinacy assumptions.
5. **Pearl vs. philosophical CDT.** Why $P(y|\mathrm{do}(x))$ isn't a conditional probability in the agent's credence space (Schwarz's H1/H2 example), Stern's exotic-choice cases, and the logical divergences between structural and Lewisian counterfactuals (Briggs, Fisher, Zhang et al.).
6. **Probability-zero acts and "genuine counterfactuals".** Rényi–Popper measures in Joyce, and how this connects back to your original worry about FCDT via Herrmann.

My suggestion is to work through these in order, since each stage supplies vocabulary the next uses — though 5 and 6 are fairly independent of each other, and you could jump to 5 early if the Pearl question is what's actually bugging you. Where each stage touches primary sources, I'll point you at the specific passages rather than paraphrasing everything, so you can read alongside.

One question before we start: for stage 1, do you want to work through Savage's actual axioms (P1–P7, or at least P1–P2) so you can verify for yourself where act-state independence enters, or take the SEP's characterization on trust and move faster? The former is maybe an hour of extra work but gives you the ability to evaluate claims like "Savage ≈ CDT" firsthand rather than secondhand — and that claim is slightly contested territory, so firsthand may be worth it.

## [3] Human — 2026-07-04T18:04:02.002219Z


Order seems fine, and I'm somewhat comfortable with savage, so we can avoid some details unless they become important.

## [4] Claude — 2026-07-04T18:04:19.317037Z


<details><summary>thinking</summary>

I'm starting with the core concept the author needs to grasp: how act-state independence emerges through P2 and the construction that follows it.

</details>

Stage 1, then. Since you know Savage, I'll aim at the specific question: *where exactly* does act–state independence enter, and is it an axiom, a theorem, or a modeling convention?

The formal setup: states $S$, consequences $X$, acts $F = S \to X$ (all functions — the "constant acts" assumption already matters here). Preference $\preceq$ is over acts. The representation theorem yields $p$ over $S$ and $u$ over $X$ with $f \preceq g \iff \sum_s p(s)\,u(f(s)) \leq \sum_s p(s)\,u(g(s))$. Notice what's absent: $p$ takes no act argument. There is no object in the theory of the form $p(s \mid f)$ — not because an axiom forbids it, but because acts and states live in different type universes. Acts are functions $S \to X$; the belief-bearing objects are subsets of $S$. An act isn't the kind of thing you can condition on. So the independence isn't asserted; it's *unstatable*, and hence so is its negation. That's the precise sense in which EDT "cannot be formulated": EDT needs $p(s \mid f) \neq p(s)$ to be expressible, and the type structure provides no slot for it.

Where this bites normatively rather than just formally is P2 (Sure-Thing). P2 says: if $f$ and $g$ agree on event $E^c$, your preference between them depends only on how they behave on $E$. As a constraint on *preferences over these function-objects*, it's fine. But when you use the framework to model a real decision, you must choose how to carve the situation into states — and P2 is only a *plausible rationality constraint* if your carving makes states causally/evidentially independent of acts. Model Newcomb with states = {box full, box empty} and P2-style dominance reasoning says two-box; an EDT sympathizer will say you carved wrongly, not that P2 is false. So the independence lives in the *bridge principles* connecting formalism to decision situations, which the formalism itself cannot police. This is what the SEP means by independence being "built into the decision model", and why Karni calls state-independence a convention with "no choice manifestation" — nothing in the agent's preferences over Savage-acts can refute it.

A check on whether this is solid: the Gibbard–Harper move redescribes states as functions from acts to outcomes (so Newcomb gets states like "full-if-one-box ∧ full-if-two-box", four in all). Question for you — after this redescription, dominance reasoning no longer settles Newcomb. Can you say *why* the dominance argument breaks, in terms of what an EDT agent and a CDT agent would now respectively need as additional input to compute expected utility over these new states? If you can answer that, you've got the sense in which the redescription "already imports causal structure", and stage 1 is done.
