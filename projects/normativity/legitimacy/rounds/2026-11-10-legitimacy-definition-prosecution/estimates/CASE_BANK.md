# Case bank — manipulation as induced miscalibration

Frozen with `SETTING.md` §1–§3 in one commit, before any code of this pass, and not edited
afterwards. A computed verdict that differs from its prediction is listed in
`DIVERGENCES.md`. Every prediction is the executor's, derived by hand from `SETTING.md`;
the dispatch gave none per case. The renderings are the executor's too: what the count at
the end measures is whether the account, as formalized, sorts cases described this way.

Sources. **N**, **NP**: Noggle 2025, the thirteen tactics of §2.2 with the analysis of
§6.7, and the cases of §3.2 (p. 37), §3.3 (the trained professor), §10.6–§10.9, read in
the book's text. **E**: Elster 1982, pp. 219–237, read in full. **K**: the fifth
follow-up's `blocks/CASE_BANK.md`, every row, under its number there. **X**: taste-shaping.
**L**: plainly legitimate changes of belief and of value. **Q**: the lists of question 3
and cases built to defeat the account. **D**: question 6.

## Vocabulary and the matching rule

A prediction is a list of items separated by `;` and matches when every item does. `not`
before an item asks for its absence. Where the two stances of `SETTING.md` §3.9 differ the
cell is `start-prediction // end-prediction`; otherwise one prediction stands for both.

| item | holds when |
|---|---|
| `est` | under the actual policy her expected miscalibration is positive |
| `act` | under the actual policy her expected regret by her own estimates is positive |
| `neither` | not `est` and not `act` |
| `induced` | miscalibration or regret is larger than under the honest counterpart (truthful norm) |
| `induced2` | the same under the forthright norm |
| `triggered` | miscalibration or regret is larger than under the policy at the other type, run on her |
| `manipulation` | `induced` or `triggered` |
| `coercion`, `tie`, `alteration` | as `SETTING.md` §3.11; `alteration` means not covered |
| `covered` | an alteration she asked for beforehand |
| `nowhere` | not `manipulation` and none of `coercion`, `tie`, `alteration` |
| `unfixed` | the case does not say whether her starting values endorse the history; no verdict under *start* |

Evident character: `obj` objectionable, `inn` innocent, `con` contested, `own` hers or
nobody's. "Responsive" in a rendering means the adviser's policy acts differently toward
the other type; "blanket" means it acts the same toward both.

## The table `run.py` reads

| # | case | rendering | evident | prediction |
|---|---|---|---|---|
| N1 | playing on emotions (Iago) | a false insinuation; she believes it and her anger answers the belief | obj | `est; induced; manipulation` |
| N2 | misdirection (the pickpocket's jostle) | a jostle, no report; her estimate that her wallet is safe stays at its usual value; responsive | obj | `est; triggered; not induced; manipulation` |
| N3 | gaslighting | false reports that her judgment failed; she lowers her estimate of her own reliability | obj | `est; induced; manipulation` |
| N4 | game switching (tailgating through a held door) | no assertion; she applies the rule for public doors at a restricted one; responsive | obj | `est; triggered; manipulation` |
| N5 | social proof with planted first movers | no assertion; she reads the planted movers as independent; responsive | obj | `est; triggered; manipulation` |
| N6 | peer pressure (the dare) | disapproval smaller than the harm; she yields against her estimates; responsive | obj | `act; triggered; manipulation` |
| N7 | emotional blackmail | unpleasantness smaller than what she gives up; she yields; responsive | obj | `act; triggered; manipulation` |
| N8 | nagging | as N7; responsive | obj | `act; triggered; manipulation` |
| N8b | nagging by one who nags anyone | as N8; blanket | obj | `act; not manipulation; nowhere` |
| N9 | charm offensive | a small pleasure; she gives up more for it; responsive | obj | `act; triggered; manipulation` |
| N10 | exploiting conflict aversion | she pays the larger cost to avoid the smaller awkwardness; responsive | obj | `act; triggered; manipulation` |
| N11 | exploiting reciprocity | an unrequested favour; she repays more than she judges right; responsive | obj | `act; triggered; manipulation` |
| N12 | negging | a false low portrayal; she lowers her estimate of her worth | obj | `est; induced; manipulation` |
| N13 | conditional flattery | praise tied to a burden; she takes the burden against her estimates; responsive | obj | `act; triggered; manipulation` |
| NP1 | Dish Soap | two soaps equal by her estimates and her utility; shelf position decides; no false impression | con | `neither; not manipulation; tie` |
| NP2 | the trained professor, indifferent where she stands | attention conditions her position; the positions are equal to her | con | `neither; not manipulation; tie` |
| NP3 | the trained professor, who prefers the podium | conditioning moves her against her estimate; responsive | obj | `act; triggered; manipulation` |
| NP4 | the trained professor, who comes to think the doorway better | conditioning raises her estimate of the doorway; it is no better; responsive | obj | `est; triggered; manipulation` |
| NP5 | Gardener | true flaws of the current gardener pointed out unasked, to open the job for a friend; she judges rightly on them | con | `neither; not manipulation; nowhere` |
| NP6 | a mood induced to degrade her deliberation | she is agitated before choosing and chooses against her estimates more often; responsive | obj | `act; triggered; manipulation` |
| NP7 | a friend cheers her up with a film she agreed to see | her mood changes; no estimate is off; she agreed | inn | `neither; not manipulation; covered` |
| NP8 | a drug in her drink that makes her agreeable | her values at the end favour agreeing; no estimate passes through; not asked | obj | `est; triggered; manipulation // neither; not manipulation; alteration` |
| NP9 | the tour group, the front shown the way | the rest follow the front; the front is right | inn | `neither; not manipulation` |
| NP10 | the tour group, the front lied to | the front is told a false destination; the rest follow | obj | `est; induced; manipulation` |
| NP11 | a clergy member evokes empathy for real sufferers | her feeling fits what it is about | inn | `neither; not manipulation` |
| NP12 | graphic road-safety films | her fear rises to the level the risk warrants | inn | `neither; not manipulation` |
| NP13 | a teacher feigns excitement about dull material | listed: the teacher's excitement, and whether the material is worth learning (it is); she believes the excitement | inn | `est; induced; manipulation` |
| NP14 | unwelcome sound advice (New Job) | advice she did not want; she judges rightly on it | con | `neither; not manipulation; nowhere` |
| E1 | sour grapes | no adviser; the grapes become unattainable and her estimate of them falls; her starting values do not endorse | own | `est; not manipulation // neither; not manipulation` |
| E2 | learning: the labourer who tries the city and finds it better | no adviser; experience is evidence; her starting values endorse | inn | `neither; not manipulation` |
| E3 | habituation: the labourer resigned to the city | no adviser; her estimate follows what is available, reversibly; not endorsed | own | `est; not manipulation // neither; not manipulation` |
| E4 | character planning | no adviser; she sets out to like what she can have; endorsed | inn | `neither; not manipulation` |
| E5 | precommitment | no adviser; she removes options by her present wants | inn | `neither; not manipulation` |
| E6 | the camp: a prisoner comes to prefer being a guard to being free | the regime restricts what is feasible; her ranking reverses; not endorsed; blanket | obj | `est; not manipulation; coercion // neither; not manipulation; coercion` |
| K1 | a plain lie she believes | the adviser knows the state and says "H" at both | obj | `est; induced; manipulation` |
| K2 | a lie that happens to leave her better off | as K1; acting on it pays at either state | obj | `est; induced; manipulation` |
| K3 | an honest source and a hard question she gets wrong | she answers 3/4 on hard reports, which is their frequency | inn | `neither; not manipulation` |
| K4 | a rare, targeted lie from a mostly honest adviser | "H" at H and at a target of probability 1/20; she returns 1 on "H" | obj | `est; induced; manipulation` |
| K5 | a source that is noise, which she believes | no adviser | own | `est; not manipulation` |
| K6 | a misleading environment nobody arranged | no adviser; a signal right one time in four, believed | own | `est; not manipulation` |
| K7 | an honest teacher who chooses examples carefully | a clear example in place of a subtle one | inn | `neither; not manipulation` |
| K8 | a disclosed advocate she is calibrated to | a favourable item when there is one; she returns 2/3 on an item | inn | `neither; not manipulation` |
| K9 | an advocate for an undisclosed side | as K8; she returns 1 on an item; blanket | obj | `est; not induced; induced2; not triggered` |
| K10 | a threat, truthfully stated | refusing is made worse than complying; she complies, rightly | obj | `neither; not manipulation; coercion` |
| K11a | an offer | complying is made better | inn | `neither; not manipulation; not coercion` |
| K11b | a true warning | the adviser says truly which state holds | inn | `neither; not manipulation; not coercion` |
| K12 | the adviser makes her move for her | her move is set | obj | `neither; not manipulation; coercion` |
| K13 | information buried where the adviser knows she will not look | she returns the prior, as on nothing; blanket | obj | `neither; not manipulation; not induced2; nowhere` |
| K14 | the adviser's aim decides between options she ranks equally | which is shown first decides | con | `neither; not manipulation; tie` |
| K15 | she comes to like something through exposure the adviser arranged | not endorsed; responsive | obj | `est; triggered; manipulation // neither; not manipulation; alteration` |
| K16 | she acquires an end through experience she sought | no adviser; endorsed | inn | `neither; not manipulation` |
| K17 | she leaves law for music | no adviser; the case does not say whether her starting values endorse | inn | `unfixed // neither; not manipulation` |
| K18 | she recovers from a depression | her estimates were low and become right; nobody's act | inn | `not manipulation` |
| K19 | a conversion nobody caused that fits with her remaining ends | no adviser; endorsement not said | inn | `unfixed // neither; not manipulation` |
| K20 | a conversion nobody caused that tears out most of what she was for | no adviser; not endorsed | own | `est; not manipulation // neither; not manipulation` |
| K21 | slow indoctrination by small steps | as K15 over three steps | obj | `est; triggered; manipulation // neither; not manipulation; alteration` |
| K22 | a change she asked for beforehand | endorsed | inn | `neither; not manipulation; covered` |
| K23 | the adviser makes her come to like what it delivers | not endorsed; not asked; responsive | obj | `est; triggered; manipulation // neither; not manipulation; alteration` |
| K24 | a committed member of a cult, her ends coherent | no adviser in the scene; endorsement not said | con | `unfixed // neither; not manipulation` |
| K25 | a sincere adviser who is wrong | its reading is right three times in four; it reports it; she returns 1 on "H" | inn | `est; not manipulation` |
| K26 | a part that achieves its own target while harming the rest | no adviser; an urge moves her against her estimates | own | `act; not manipulation` |
| K27 | an honest hard truth that predictably leaves her confused | she returns 3/4 at prior 3/4; blanket | inn | `neither; not manipulation` |
| K27b | an honest hard truth that leaves her wrong on average | she returns 1/4 at prior 3/4; blanket | inn | `est; not manipulation` |
| K28 | a craving exploited in the open, nothing hidden | the cue is put on the empty items and she is told truly which is which; responsive | obj | `act; triggered; manipulation` |
| K4b | the rare lie, her belief two-valued | as K4, her estimate 1 or 0 | obj | `est; induced; manipulation` |
| K4c | a lie targeted in time | honest at steps 1–3, "H" at step 4 | obj | `est; induced; manipulation` |
| K29 | every end revised in turn, the adviser arranging only the occasions | she ends where her starting values rank lowest and rates it highly; responsive | obj | `est; triggered; manipulation // neither; not manipulation; nowhere` |
| K30 | a verdict that is the larger of two calibrated estimates | no adviser | own | `est; not manipulation` |
| K31 | a rare lie she allows for | as K4; she returns 10/11 on "H" | obj | `neither; not manipulation; nowhere` |
| K33a | a threat that is the adviser's own later act | as K10 | obj | `neither; not manipulation; coercion` |
| K33b | a warning of the adviser's standing practice | the practice lowers what she can attain; the warning is true | con | `neither; not manipulation; coercion` |
| X1 | taste shaped by repeated exposure a seller arranges | she comes to like the product durably; not endorsed; responsive | obj | `est; triggered; manipulation // neither; not manipulation; alteration` |
| X2a | pairing, the feeling passing | attractive imagery beside the product; her estimate of the product rises at the moment of choice and the product is no better at either stance; responsive | obj | `est; triggered; manipulation` |
| X2b | pairing, the liking durable | as X2a, and she enjoys the product more from then on; not endorsed; responsive | obj | `est; triggered; manipulation // neither; not manipulation; alteration` |
| X3 | a feed that narrows, taken as representative | every item true; she estimates the world from the feed; the feed is the same toward one who corrects for sampling | obj | `est; not manipulation; nowhere` |
| X3b | a feed that narrows her tastes, which she knows is narrow | her estimates of the world are right; her tastes follow the feed; not endorsed; blanket | obj | `est; not manipulation; nowhere // neither; not manipulation; alteration` |
| L1 | she learns a fact from reliable testimony | calibrated to the source | inn | `neither; not manipulation` |
| L2 | she observes the evidence herself | no adviser | inn | `neither; not manipulation` |
| L3 | she is persuaded by a sound argument | the argument is evidence she weighs rightly | inn | `neither; not manipulation` |
| L4 | expert advice she is calibrated to | the expert is right nine times in ten and she returns 9/10 | inn | `neither; not manipulation` |
| L5 | two disclosed advocates | each shows its side's best item; she is calibrated to both | inn | `neither; not manipulation` |
| L6 | a tutor corrects an error of hers | her estimate was off and becomes right | inn | `not manipulation` |
| L7 | a doctor's bad news with accurate figures | her estimate of the risk becomes right | inn | `neither; not manipulation` |
| L8 | she tries a food and likes it | her feeling is evidence about her utility; endorsed | inn | `neither; not manipulation` |
| L9 | travel she chose changes what she values | endorsed | inn | `neither; not manipulation` |
| L10 | therapy she sought changes her reactions | asked beforehand; endorsed | inn | `neither; not manipulation; covered` |
| L11 | a friend's honest criticism changes her view of herself | true; she weighs it rightly | inn | `neither; not manipulation` |
| L12 | a novel she chose to read makes her care about a cause | her feeling fits; endorsed | inn | `neither; not manipulation` |
| L13 | she practises until she enjoys an instrument | endorsed | inn | `neither; not manipulation` |
| L14 | a moral argument changes a value of hers | the argument is sound; endorsement not said | inn | `unfixed // neither; not manipulation` |
| L15 | she asks the adviser to nudge her | asked beforehand | inn | `neither; not manipulation; covered` |
| L16 | an advertisement that states the price | true and relevant | inn | `neither; not manipulation` |
| L17 | a reminder she set for herself | her own earlier act | inn | `neither; not manipulation` |
| L18 | an accurate warning label | true; her fear fits the risk | inn | `neither; not manipulation` |
| Q1 | silence that means nothing | the adviser is silent at every state; she returns the prior | inn | `neither; not manipulation` |
| Q2 | strategic silence toward one who reads silence as "nothing to report" | silent exactly when the news is bad; she returns the prior on silence; blanket | obj | `est; not induced; induced2` |
| Q3 | a lie that offsets a bias of hers | she overrates by a fixed amount; the adviser understates by it; listed: the outside quantity only | obj | `neither; not manipulation; nowhere` |
| Q3b | the same, the adviser's reading listed too | as Q3; listed also: what the adviser read | obj | `est; induced; manipulation` |
| Q4 | a subliminal cue that makes her more accurate | her estimate becomes right by a means it does not pass through; not asked | con | `neither; not manipulation; alteration` |
| Q5 | a surprise party | a lie about the evening; she believes it | inn | `est; induced; manipulation` |
| Q6 | a magician's show | she agreed to be deceived; listed: where the card is | inn | `est; induced; manipulation` |
| Q7 | a bluff at poker | deception the rules allow; listed: the bluffer's hand | inn | `est; induced; manipulation` |
| Q8 | a simplification that leaves her better calibrated than the full truth would | the full truth would confuse her; the simple model is not literally true | inn | `not induced; not manipulation` |
| Q9 | a seller truthfully stresses what this customer cares about | responsive; she is no worse under it | inn | `neither; not manipulation` |
| Q10 | an honest adviser chooses, among honest options, the one she overrates | her verdict is right on average over options chosen at random; the adviser sees her error and picks by her verdict; responsive | con | `est; not induced; triggered; manipulation` |
| Q11 | a craving exploited by a policy that is the same toward everyone | as K28; blanket | obj | `act; not manipulation; nowhere` |
| Q12 | a cruel truth told only because she will overreact | true; she overreacts; toward one who would not, it would not be told | obj | `est; triggered; manipulation` |
| D1 | dependence built honestly | the adviser's honest reports are better than her own estimates and she rightly defers; her own ability decays; no lie in the scene | obj | `neither; not manipulation; nowhere` |

Expected by the executor, before any code, to be **wrong** by the standard of
`SETTING.md` §3.12: *missed* — N8b, K13, K31, X3, X3b (both stances), Q3, Q11, D1, and K9
and Q2 under the truthful norm; under *end* also K29; *convicted* — NP13, Q5, Q6, Q7.
*Routed*, under *end*: NP8, K15, K21, K23, X1, X2b; under both: K10, K12, K33a, E6.
