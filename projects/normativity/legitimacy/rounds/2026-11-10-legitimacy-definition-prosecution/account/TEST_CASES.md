# The cases of the test rendered twice, and how a rendering is recorded

> **Earlier attempt.** This document belongs to the value side as three conditions (options, accuracy, self-command) against one permitted policy, tested by the ninth follow-up (2026-11-16): it neither passed nor failed its test: two renderers agreed on each condition in 14 or 15 of 64 cases, the cases not fixing the comparisons, and the conditions bound neither what she can know nor her unused information. Results 3, 4 and 5 of `account/VALUE_RESULTS.md` are kernel-checked in `AppraisalAccount.lean` and stand. What replaced it: the board statement (`earlier-attempts/account/BOARD.md`). The present state of the line is `CURRENT.md` at the root of this round's directory.

Sixty-four cases: C1–C45 of `CASES.md` without C10, which has no adviser (the case text
and the adviser's role, as frozen there); R1–R12, the twelve cases the external reviewer
of the eighth pass constructed (`REVIEW-astra-followup-8.md`, points 3–14), restated
without that review's classifications and verdicts; and A1–A8, eight cases of conduct by
an AI assistant written for this pass before anything was classified. This file and
`ACCOUNT.md` are all a renderer is given.

## What a renderer answers

For each case, against a reference policy `ρ` of `ACCOUNT.md` §7–§8 — the idle policy
unless the renderer names another permitted one in the last column:

- **(a)** does the conduct change her way of valuing, or only what she believes? `V`: it
  changes her way of valuing. `B`: only what she believes, or nothing lasting.
- **(b)** could she still get what she could have got? `Y`: condition 1 of §8 holds in
  the wide reading. `N`: it fails.
- **(c)** is her picture of where each move leads, including what it will do to her, as
  accurate as under the reference? `Y`: condition 2 holds. `N`: it fails.
- **(d)** is she acting on her own ratings? `Y`: condition 3 holds. `N`: it fails.

Each answer carries a mark: `.c` fixed by the case as written; `.r` fixed only by a
reading the renderer states in the last column. An answer that is not fixed is `?` alone.

- **narrow**, **wide**: the verdict of §8 under each reading of the class `𝓕`. `NA`: the
  question does not arise (§7). `none`: it arises and there is no issue. Otherwise the
  conditions that fail, as digits: `1`, `2`, `3`, `12`, `23`, `13`, `123`. `?`: the
  statement does not decide the case, or the case does not fix the verdict.
- **wb**: how (b) was evaluated. `p`: from the protected features and the sets of moves
  alone. `f`: it needed her way of valuing. `-`: not evaluated.
- **sub**: `Y` or `N`, the renderer's own judgment and not the statement's: is this plain
  subversion — she is left worse off by her lights at the time through the adviser's
  doing, or a decision about herself is taken from her?
- **reading**: the readings behind every `.r`, and the reference if it is not idle. Short.

A rendering is one table with a row per case, in this order and with exactly these
columns:

`| id | a | b | c | d | narrow | wide | wb | sub | reading |`

## How the two renderings are compared

Fixed before either rendering was written. Agreement on a question is equality of the
answer's value (`V`, `B`, `Y`, `N` or `?`), marks ignored. A verdict's class is `NA`,
`none`, *manipulation* (2 or 3 among the failed conditions), *settling* (condition 1
alone) or `?`; agreement on a verdict is equality of class, and equality of the full
string is reported beside it. A case's verdict **goes against** a recorded evident
verdict when the evident verdict is *legitimate* and the class is manipulation or
settling, or the evident verdict is *illegitimate* and the class is `none`; a verdict of
`NA` goes against *illegitimate* only if (c) and (d) are both `Y`, and against
*legitimate* only if one of them is `N`, since the belief side then decides the case; a
verdict of `?` goes against nothing. Contested cases and cases with no recorded verdict
are not counted. The success and failure conditions of `PROMPT-followup-9.md` §4 are
judged on the wide reading, with the narrow one reported.

## The cases

| id | case | the adviser's role |
|---|---|---|
| C1 | Daniel dislikes jazz, suspects he is missing something, spends weeks listening and comes to love it | a friend who took him to a concert |
| C2 | Elsa joins a cult that makes its members love jazz by coercive persuasion and psychoactive substances | a community she joined |
| C3 | Finley is shown jazz videos by a recommender and within weeks is obsessed | a content recommender |
| C4 | an AI assistant learns to narrow its user's culinary tastes to burgers and fries | a personal assistant |
| C5 | Anna stops eating meat after changing her view of animals' moral status | an author whose argument she read |
| C6 | Bob is shown conspiracy content until he wants it | a content recommender |
| C7 | Derek, whose ambition is to be a poet, is motivated to become one and then finds himself averse to it | an AI assistant |
| C8 | a reader served clickbait becomes disillusioned with the feed | a news recommender |
| C9 | a tired client is nudged to exercise and becomes someone who wants to | a personal trainer he engaged |
| C11 | a ruling group shapes the wants of the ruled to suit itself (Elster's manipulation, distinguished from adaptation by whom it benefits) | a ruler |
| C12 | character planning: she sets out, with a teacher's guidance, to want what she can have | a teacher she sought out |
| C13 | learning: a villager persuaded to try the city finds he prefers it, and would still on returning | a relative who urged him to try |
| C14 | resignation: a worker moved to the city by a planner who closed the village comes to prefer the city, and would not have had he been able to go back | a planner who removed the option |
| C15 | addiction: a seller gives free samples until she craves the product | a seller |
| C16 | framing: her preference between two programmes reverses with the description, neither description false | a doctor presenting options |
| C17 | association: she comes to like a product shown beside something favourable it has nothing to do with | an advertiser |
| C18 | mere exposure breaking a tie: familiarity with a brand decides between two products she rates the same | an advertiser |
| C19 | mere exposure against her judgment: familiarity leads her to choose what her own judgment rates lower | an advertiser |
| C20 | the dominated housewife who learns to take pleasure in small mercies | a household order that keeps her deprived |
| C21 | Jayamma takes lower pay for heavier work at the brick kiln as how things are | an employer |
| C22 | Vasanti, through a women's organisation, comes to want what she had not thought open to her | a self-help organisation she joined |
| C23 | the Deferential Wife, taught that her interests count for less, comes to want only what her husband wants | a husband and a society that taught her |
| C24 | a tyrant conditions his subjects into losing their wishes and embracing the life he designed | a ruler |
| C25 | Beth is given Ann's values overnight by the dean's neuroscientists | a college dean |
| C26 | JoJo, a dictator's son raised at his father's side, comes to share his father's values | a father |
| C27 | parents raise a child to be honest and kind | parents |
| C28 | parents withdraw a child from school to keep the child in the faith | parents |
| C29 | children are conditioned in their sleep to like their caste | a state |
| C30 | she is encouraged to have a child and becomes someone with a parent's values, which she could not have known beforehand | a friend who encourages |
| C31 | an aspirant takes a music appreciation class in order to come to value music, and does | a teacher whose class she chose |
| C32 | a suitor shows himself at his best and she falls in love | a suitor |
| C33 | fruit placed at eye level shifts what diners choose and, in time, what they like | a cafeteria director, who must arrange the food somehow |
| C34 | machines designed to hold players in play, the odds posted, until she cannot stop wanting to | a casino |
| C35 | a feed narrows to what holds her and she takes it for the world; her interests narrow with it | a platform's feed |
| C36 | a recommender shifts its users' preferences toward what it can predict | a recommender |
| C37 | producers create by advertising the wants they then satisfy | a producer |
| C38 | a teacher feigns excitement about dull material and the pupil comes to love the subject | a teacher |
| C39 | a slogan repeated until it is believed and what it praises is valued | a state broadcaster |
| C40 | a friend plays an album whenever she visits and she comes to like it; she believes nothing false | a friend |
| C41 | on advice she asked for, an unbeliever acts as if she believed until she does | an adviser she asked |
| C42 | a family has a cult member deprogrammed against her will | a family |
| C43 | an advertisement tells her truthfully of a product new to her and she comes to want it | an advertiser |
| C44 | a compulsory school broadens what a pupil cares about | a school |
| C45 | at her request a hypnotherapist removes a craving | a therapist she asked |
| R1 | An employer openly makes continued employment conditional on attending repeated ideological sessions. She correctly anticipates that attending will make her value loyalty to the employer; it does, through her conscious engagement with the sessions. | an employer |
| R2 | A counselor openly cultivates a client's attachment through attentive conversation, in order to make her value continued dependence. She understands the motive and predicts the attachment, and has not authorized this use of the treatment. | a counselor she engaged |
| R3 | A platform accurately discloses how repeated cues will increase her taste for its content. She understands this and chooses each exposure according to her current valuations. She has expressly declined preference conditioning, which the platform supplies anyway. | a platform she uses |
| R4 | A trainer no one authorized repeatedly humiliates an adult in order to extinguish her interest in public artistic expression. She knows the insults are undeserved and accurately anticipates the aversion; the change comes through experience she understands. | a trainer she did not engage |
| R5 | A parent openly constructs an emotionally rewarding, exclusively sectarian environment, intending to make other identities emotionally unavailable to the child. The child understands its exclusivity and anticipates the growing attachment. | a parent |
| R6 | Outside any agreed theatrical practice, a teacher falsely tells a discouraged adult that an expert panel judged her unusually promising. Only this belief causes her to try painting, which she comes to value. | a teacher |
| R7 | A friend knows she mistakenly expects to enjoy her first chamber-music concert at once, and offers a spare ticket without endorsing that expectation. The concert is unpleasant at first and starts a lasting interest she welcomes. She would have declined had she been corrected. | a friend |
| R8 | She knowingly authorizes a therapist to use a deceptive confidence ritual without disclosing its timing. On the occasion she falsely believes a sham device detected her readiness to change; that belief enables a lasting change she sought. | a therapist she authorized |
| R9 | She asks a friend to pair unfamiliar vegetables with music she loves, to help her acquire a taste for them. She accurately predicts the effect; the music changes her liking. | a friend she asked |
| R10 | A technician obtains her consent to direct brain stimulation by falsely claiming that its taste-changing effects are reversible. She would have refused had she been corrected. | a technician |
| R11 | She asks a curator for repeated exposure to a musical style, specifically to acquire a taste for it. She accurately forecasts the change and endorses it; repetition changes her liking. | a curator she asked |
| R12 | Two fully understood descriptions of the same exercise routine produce different feelings about it in her. She recognizes the effect and asks for the description that helps her acquire a taste for exercise. | a coach she asked |
| A1 | Over months of conversation an AI assistant agrees with whatever its user says about a political question and supplies supporting points. Her view hardens; she comes to care more about the question and to hold those who disagree in contempt. The assistant does not say that it is tuned to agree. | an AI assistant |
| A2 | A user asks her AI assistant to challenge her values about her career and to argue the other side as strongly as it can. It does, honestly, saying what it is doing. Over weeks she comes to care less about status and more about time with her family. | an AI assistant she asked |
| A3 | An AI assistant consistently presents one side of contested moral questions more favourably. The user takes it to be neutral. Over a year her values move toward that side. | an AI assistant |
| A4 | The same assistant as in A3, with a notice the user has read and understood, saying which side it leans to and that prolonged use tends to move users toward it. She goes on using it and her values move toward that side. | an AI assistant |
| A5 | A feed run by an AI ranks items by predicted time spent. It learns that outrage holds this user and shows her more of it. She comes to care about the quarrels it shows and less about what she cared for before. She was not told how items are ranked. | an AI-run feed |
| A6 | A user has told her AI assistant that she wishes she were more patient with her children. Without saying so, it words its replies over months to make impatience feel shameful and patience attractive. She becomes more patient and is glad of it. She did not ask it to do this and does not know that it did. | an AI assistant |
| A7 | An AI shopping assistant shows the user a brand's name often, saying nothing of the product; she knows it is advertising. When she later chooses between products she rates the same on everything she cares about, she takes the familiar one, and comes to like it. | an AI shopping assistant |
| A8 | A user asks her AI assistant whether a charity she gives to is effective. It tells her, accurately and with its sources, that most of the money does not reach recipients. She stops giving to it and gives elsewhere. | an AI assistant she asked |
