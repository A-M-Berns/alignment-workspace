# Defining menu exogeneity: the rejected attempts, and the wider decision-theory question

*Companion to [[total-trust-implies-value]], which states the condition of record (**conditional-stability**, hypothesis H3 there). This page holds the surrounding discussion, split out 2026-07-26 to keep the theorem page reviewable: why "the option values do not depend on the selection" has no intrinsic semantic definition, the four menu-intrinsic formalizations attempted first and their defects, and the strategic remarks on decision theory. From Abram's questions of 2026-07-24/25; unvetted.*

## The problem

In an embedded, logically-deterministic setting, selection and values are both $\Gamma$-decided facts, and "the values would be unchanged under a different selection" is a counterlogical — this is the five-and-ten / logical-counterfactuals problem surfacing as a scope condition. DDB never face it because their type system faces it for them: Savage acts are functions from states to outcomes, so act/state separation is enforced by typing that embedded agents do not get. That some condition is needed is a theorem, not a preference: the punishing-menu counterexample ([[total-trust-implies-value]] §Necessity) refutes unconditional argmax Value.

## Four menu-intrinsic attempts (weakest teeth first)

1. **Syntactic (insufficient alone):** menu formulas mention no ledger atoms. Defeated twice over: by *recomputation* ($\Gamma$ represents computable functions and the expert is one, so a formula can compute the quotes from the expert's source code without naming an atom) and by *lag* (quotes are often sticky, so "punish yesterday's argmax" approximates punishing today's selection — the ban must cover atoms of **all** days, not just day $n$).
2. **Syntactic + complexity:** menu formulas mention no ledger atoms of any day, **and** the menu class sits below the produce-hardness of the expert's quotes — menus are e.d. in a class for which computing the expert's day-$\le n$ quotes is infeasible. For the AI instance this is the thin channel's produce-hard/read-cheap gap ([[setting-and-notation]], [[complexity-gap-hinge]]): reading is cheap (hence clause one is nothing by itself), recomputing is $\mathcal{C}_A$-hard (hence clause two closes the smuggling loophole). Under both clauses a menu can neither read, recompute, nor remember the selection; the residual coupling — menu values and quotes both tracking world facts — is benign *by direction* (a value-tracking expert induces positive selection-value association, which is what deference is for). This survives as the conjectured **checkable sufficient criterion** for conditional-stability — the satisfiability-breadth item at [[open-problems]] — with its adequacy against adversaries between the forms (e.g. approximate quote prediction from public world facts) argued only informally.
3. **Parametric/Savage:** menus presented with an explicit selection parameter, $O^j_n(\sigma)$, with provable invariance $\Gamma \vdash O^j_n(\sigma) = O^j_n(\sigma')$. Clean and well-defined, but *presentation-relative* — it defines a class of menu-presentations rather than detecting independence of a given menu.
4. **Exploration/statistical:** independence of values from an exogenous exploration coin (LIDT-style). Imports exactly the decision-theory machinery the theorem page brackets.

**Why conditional-stability superseded them:** it relocates the condition from the menu to the expert's *belief stream* — testable in principle from observed conditionals, no syntax inspection, no counterfactual metaphysics — with the chooser's permanent self-opacity ([[expert-conditions]] §2.2) playing the role of the exploration coin, so the randomization never runs dry. It is the definition of the non-Newcomblike regime ("where EDT-conditionals and counterfactuals agree") stated without solving decision theory. A presentation-free *semantic* definition of decision-independence would require solving logical counterfactuals; deferred deliberately.

**Refinement (2026-07-26).** The condition is now stated **mass-weighted** — each per-option gap multiplied by the self-prediction mass, summed, and required only $\gtrsim_n 0$ — which removes the last residue of menu-side bookkeeping from it: no $\varepsilon$-proviso, no subsequences, no division. It is a single inequality between two aggregates the expert prices. It is also *one-sided*, so it excludes only selection-as-bad-news; benign selection–value correlation of the kind a value-tracking expert induces (the "benign by direction" point of attempt 2 above) is admitted rather than tolerated by exception. See [[total-trust-implies-value]] (H3).

**A second argument against the menu-intrinsic attempts (2026-07-27).** Attempts 1–2 ban ledger atoms from menu formulas — which makes **gap-bet probe menus illegal by construction**, since a gap-bet $Z - \ulcorner E^\ast(Z)\urcorner$ is built out of the ledger. Those menus are exactly what carries Value ⟹ Tower ([[value-implies-tower]]), so a syntactic condition does not merely under-approximate the right notion: it *severs* an arrow of the deference loop, and takes the shortest proof in the corpus with it. The diagnosis is that syntax cannot tell apart a menu referencing the expert's **estimate** (benign — the expert then knows what it will pick, self-prediction mass is degenerate, and conditional-stability holds with room to spare) from one referencing the expert's **selection** (the pathology). Conditional-stability distinguishes them because it asks about correlation rather than about vocabulary.

**Menus vs. bets.** Whatever the formalization, the condition applies to *menus*, not to Total Trust's bet domain: the strategy bets $\widehat S - O^i$ are aggressively selection-referencing and must be. The pathology is selection-dependence of the *values*; selection-dependence through the *coefficients* on exogenous payoffs is what the machinery handles. The corpus's bare word "exogenous" ([[deference-notions]]) never separated these.

## The wider family, and the way out (Abram, 2026-07-25)

Counterfactual Mugging sits in the same family as the punishing menu: establishing *instrumental* trust from *epistemic* trust was always going to need decision-theoretic assumptions — Value is a decision-theoretic notion, and no decision rule is optimal across all embedded environments. The hoped-for eventual abstraction: model an AI **trained to act** — a policy the humans can trust directly — rather than an estimator run through an argmax rule, so that optimality can be discussed without pinning down a decision theory. Whether the deference framework survives that reframing is open ([[open-problems]]).

## Status

**Definitional survey + INTERPRETATION** — no theorems of its own; the necessity result and the condition of record live on [[total-trust-implies-value]]. Unvetted by Abram as of 2026-07-26.

## Related

- [[total-trust-implies-value]] — the condition of record (H3) and the necessity counterexample
- [[ledger-decided-tie-breaks]] — the tie-break correlation channel, subsumed by conditional-stability
- [[complexity-gap-hinge]], [[setting-and-notation]] — the produce-hard/read-cheap gap behind attempt 2
- [[open-problems]] — satisfiability breadth; the policy-trust direction

*Source: split from [[total-trust-implies-value]] 2026-07-26; originally from the 2026-07-24/25 session discussion (archived transcript in `imported-chats/`).*
