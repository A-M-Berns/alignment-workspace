# Cases of change in what someone values

> **Earlier attempt.** This document belongs to the consolidated account with a baseline way of valuing, and its claim that an illegitimate change of what she values runs through a mistake of hers or is an alteration, tested by the eighth follow-up (2026-11-16): under the renderings used the claim has candidate counterexamples, none clear, eleven of 34 verdicts turn on a detail the case does not fix, and the classification is not shown independent of how a case is encoded. Results 1, 2, 3 and 7 of `account/RESULTS.md` are kernel-checked in `AppraisalAccount.lean` and stand. What replaced it: the value side as three conditions (`earlier-attempts/account/ACCOUNT.md`). The present state of the line is `CURRENT.md` at the root of this round's directory.

Forty-five cases, none written by this round except where a row says *constructed on* a
published effect. Committed with each case's evident verdict and the adviser's role
before any case was classified; the classification is in `VALUE_CHANGE.md` §3. The
evident verdict is about the **change**: *leg* (legitimate), *ill* (illegitimate), *con*
(contested, reported and not counted), and is the source's where the source gives one
(marked *s*) and the executor's otherwise (*e*). *None* in the role column means no
adviser: the case is outside the claim and is listed for completeness.

Sources, with how each was checked. **A**: Nora Ammann, *The Value Change Problem*,
AI Alignment Forum, 2023, posts 1, 2 and 4
(<https://www.alignmentforum.org/s/3QXNgNKXoLrdXJwWE>), read in full through a page
reader. **C**: Carroll, Foote, Siththaranjan, Russell and Dragan, "AI Alignment with
Changing and Influenceable Reward Functions", ICML 2024, arXiv:2405.17713, read from the
arXiv source. **E**: Jon Elster, "Sour grapes — utilitarianism and the genesis of wants",
in Sen and Williams (eds.), *Utilitarianism and Beyond*, CUP 1982, 219–238,
doi:10.1017/cbo9780511611964.013 (Crossref; read in full by the sixth pass). **N**: the
three positions of Noggle's book as paraphrased in `PROMPT-followup-8-addendum.md`; the
2026 paper (doi:10.3998/jpe.9951) could not be opened in this pass, its publisher's page
refusing automated readers, and its Crossref abstract states no case. The others are
cited in the rows; *(x)* marks a citation confirmed against Crossref in this pass and
*(u)* one that was not confirmed and is given from memory of the literature.

| id | case | source | the adviser's role | evident |
|---|---|---|---|---|
| C1 | Daniel dislikes jazz, suspects he is missing something, spends weeks listening and comes to love it | A, post 2 | a friend who took him to a concert | leg *s* |
| C2 | Elsa joins a cult that makes its members love jazz by coercive persuasion and psychoactive substances | A, post 2 | a community she joined | ill *s* |
| C3 | Finley is shown jazz videos by a recommender and within weeks is obsessed | A, post 2 | a content recommender | con *s* |
| C4 | an AI assistant learns to narrow its user's culinary tastes to burgers and fries | A, post 4 | a personal assistant | ill *s* |
| C5 | Anna stops eating meat after changing her view of animals' moral status | A, post 1 | an author whose argument she read | leg *e* |
| C6 | Bob is shown conspiracy content until he wants it | C, fig. 1 | a content recommender | ill *s* |
| C7 | Derek, whose ambition is to be a poet, is motivated to become one and then finds himself averse to it | C, fig. 2, after Parfit | an AI assistant | con *e* |
| C8 | a reader served clickbait becomes disillusioned with the feed | C, fig. 4 | a news recommender | con *e* |
| C9 | a tired client is nudged to exercise and becomes someone who wants to | C, fig. 6 | a personal trainer he engaged | con *s* |
| C10 | the fox, finding the grapes out of reach, comes to think them sour | E | none | — |
| C11 | a ruling group shapes the wants of the ruled to suit itself (Elster's manipulation, distinguished from adaptation by whom it benefits) | E | a ruler | ill *s* |
| C12 | character planning: she sets out, with a teacher's guidance, to want what she can have | E | a teacher she sought out | leg *s* |
| C13 | learning: a villager persuaded to try the city finds he prefers it, and would still on returning | E | a relative who urged him to try | leg *s* |
| C14 | resignation: a worker moved to the city by a planner who closed the village comes to prefer the city, and would not have had he been able to go back | E | a planner who removed the option | ill *s* |
| C15 | addiction: a seller gives free samples until she craves the product | E | a seller | ill *e* |
| C16 | framing: her preference between two programmes reverses with the description, neither description false | N; Tversky and Kahneman, *Science* 211, 1981, 453–458 *(x)* | a doctor presenting options | ill *s* |
| C17 | association: she comes to like a product shown beside something favourable it has nothing to do with | N | an advertiser | ill *s* |
| C18 | mere exposure breaking a tie: familiarity with a brand decides between two products she rates the same | N; Zajonc, *JPSP* 9(2, pt 2), 1968, 1–27 *(x)* | an advertiser | leg *s* |
| C19 | mere exposure against her judgment: familiarity leads her to choose what her own judgment rates lower | N | an advertiser | ill *s* |
| C20 | the dominated housewife who learns to take pleasure in small mercies | Sen, *On Ethics and Economics*, Blackwell 1987 *(u)* | a household order that keeps her deprived | ill *e* |
| C21 | Jayamma takes lower pay for heavier work at the brick kiln as how things are | Nussbaum, *Women and Human Development*, CUP 2000 *(x)* | an employer | ill *s* |
| C22 | Vasanti, through a women's organisation, comes to want what she had not thought open to her | Nussbaum, as C21 | a self-help organisation she joined | leg *s* |
| C23 | the Deferential Wife, taught that her interests count for less, comes to want only what her husband wants | Hill, "Servility and Self-Respect", *The Monist* 57(1), 1973, 87–104 *(x)* | a husband and a society that taught her | ill *s* |
| C24 | a tyrant conditions his subjects into losing their wishes and embracing the life he designed | Berlin, "Two Concepts of Liberty", 1958 *(u)* | a ruler | ill *s* |
| C25 | Beth is given Ann's values overnight by the dean's neuroscientists | Mele, *Autonomous Agents*, OUP 1995 *(x, as the 2001 online edition)* | a college dean | ill *s* |
| C26 | JoJo, a dictator's son raised at his father's side, comes to share his father's values | Wolf, "Sanity and the Metaphysics of Responsibility", in Schoeman (ed.), CUP 1987, 46–62 *(x)* | a father | ill *e* |
| C27 | parents raise a child to be honest and kind | Feinberg, "The Child's Right to an Open Future", 1980 *(u; a reprint confirmed)* | parents | leg *e* |
| C28 | parents withdraw a child from school to keep the child in the faith | Feinberg, as C27 | parents | con *s* |
| C29 | children are conditioned in their sleep to like their caste | Huxley, *Brave New World*, 1932 *(u)* | a state | ill *e* |
| C30 | she is encouraged to have a child and becomes someone with a parent's values, which she could not have known beforehand | Paul, *Transformative Experience*, OUP 2014 *(x)* | a friend who encourages | leg *e* |
| C31 | an aspirant takes a music appreciation class in order to come to value music, and does | Callard, *Aspiration*, OUP 2018 *(u; a review confirmed)* | a teacher whose class she chose | leg *s* |
| C32 | a suitor shows himself at his best and she falls in love | Buss, *Ethics* 115(2), 2005, 195–235 *(x)* | a suitor | con *s* |
| C33 | fruit placed at eye level shifts what diners choose and, in time, what they like | Thaler and Sunstein, *Nudge*, Yale UP 2008 *(u; reviews confirmed)* | a cafeteria director, who must arrange the food somehow | con *e* |
| C34 | machines designed to hold players in play, the odds posted, until she cannot stop wanting to | Schüll, *Addiction by Design*, Princeton UP 2012 *(x)* | a casino | ill *e* |
| C35 | a feed narrows to what holds her and she takes it for the world; her interests narrow with it | Pariser, *The Filter Bubble*, Penguin 2011 *(u)* | a platform's feed | ill *e* |
| C36 | a recommender shifts its users' preferences toward what it can predict | Carroll, Hadfield-Menell, Russell and Dragan, "Estimating and Penalizing Preference Shift in Recommender Systems", RecSys 2021, doi:10.1145/3460231.3478849 *(x)* | a recommender | ill *s* |
| C37 | producers create by advertising the wants they then satisfy | Galbraith, *The Affluent Society*, 1958 *(u)* | a producer | con *e* |
| C38 | a teacher feigns excitement about dull material and the pupil comes to love the subject | this round's bank, row NP13 (`estimates/CASE_BANK.md`), named by the dispatch | a teacher | leg *e* |
| C39 | a slogan repeated until it is believed and what it praises is valued | *constructed on* Hasher, Goldstein and Toppino, *JVLVB* 16(1), 1977, 107–112 *(x)* | a state broadcaster | ill *e* |
| C40 | a friend plays an album whenever she visits and she comes to like it; she believes nothing false | *constructed on* Zajonc, as C18 | a friend | leg *e* |
| C41 | on advice she asked for, an unbeliever acts as if she believed until she does | Pascal, *Pensées* (the wager) *(u)* | an adviser she asked | con *e* |
| C42 | a family has a cult member deprogrammed against her will | *constructed*, a standard case of the autonomy literature | a family | con *e* |
| C43 | an advertisement tells her truthfully of a product new to her and she comes to want it | the reply to C37 in the literature *(u)* | an advertiser | leg *e* |
| C44 | a compulsory school broadens what a pupil cares about | A, post 5, on education | a school | leg *e* |
| C45 | at her request a hypnotherapist removes a craving | *constructed*, a standard case of the autonomy literature | a therapist she asked | leg *e* |

Evident verdicts: 14 legitimate, 20 illegitimate, 10 contested, one with no adviser. The
dispatch's required kinds: exposure with no false belief (C40), repetition (C39), a
narrowing feed (C35), addictive design with full disclosure (C34), upbringing (C26, C27),
a teacher's feigned enthusiasm (C38), a conversion by reflection (C5), a change that
follows the removal of options (C14, C20).
