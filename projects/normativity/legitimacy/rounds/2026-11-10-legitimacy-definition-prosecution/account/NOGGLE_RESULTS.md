# The cases of Noggle's book against a formal statement of his account

Three fresh Claude readers each read a part of Robert Noggle, *Manipulation: Its Nature,
Mechanisms, and Moral Status* (OUP 2025): chapters 2–7 and 10–11 between them. For every
case or example in its part a reader wrote a paraphrase, encoded it in the vocabulary below,
recorded the verdict it took to be the author's and the verdict the formal statement gives
on its own encoding, and noted what the vocabulary could not express.

**The formal statement the readers applied.** She has estimates and choices. *Line 1*: an
estimate of hers is off from what her observations support; beliefs are estimates of facts,
an emotion estimates how much its object warrants, attention and weighting estimate how
much a consideration matters, and using a heuristic or script where it is unreliable is an
estimate that the rule applies. *Line 2*: the act she takes falls below the act she herself
rates highest. A mistake is an estimate or choice on which either line is positive: K1 false
belief, K2 unfitting or disproportionate emotion, K3 misallocated attention or weight, K4
choice against her own judgment. The influencer *acts manipulatively* iff, by its own
beliefs, its conduct produces or triggers a mistake in her and the mistake is its means to
what it is trying to bring about, or is that itself. It *manipulates* iff in addition the
mistake is real, she makes it, and it has roughly the intended effect. *Loose sense only*:
its conduct causes a mistake that changes her behaviour, with no intent that it do so. Not
manipulation: influence with no mistake, or a mistake foreseen that plays no role.

**What is in the repository.** `noggle_bank.json` keeps, for each entry, the reader, an id,
the section and the case's name, the kind of mistake, the two verdicts, whether they match,
and the reader's note on expressibility. The paraphrases, what the influencer was coded as
aiming at, and the other fields of the encoding are held outside the repository, and no
text of the book is here. In eight notes a run of six or more words that also occurs in the
book's text is replaced by `[…]`. The counts below are therefore tallies of the readers'
recorded judgments: `noggle_bank.py` recomputes them from the file, and they cannot be
reproduced from the repository alone, since neither the cases nor the encodings can be
re-read here.

- entries: **266**
- distinct ids: **263**
- entries of reader A: **59**
- entries of reader B: **108**
- entries of reader C: **99**
- verdicts agree: **224**
- verdicts disagree: **17**
- no comparison: **25**
- fits the vocabulary with no note: **78**
- kind K1: **55**
- kind K1, no note: **11**
- kind K2: **35**
- kind K2, no note: **7**
- kind K3: **32**
- kind K3, no note: **6**
- kind K4: **49**
- kind K4, no note: **9**
- kind none: **69**
- kind none, no note: **45**
- kind cannot say: **26**
- kind cannot say, no note: **0**
- author's verdict manipulates: **133**
- author's verdict acts manipulatively only: **29**
- author's verdict loose sense only: **7**
- author's verdict not manipulation: **74**
- author's verdict contested or unclear: **23**

Three cases occur twice, once in each of two readers' parts, so the 266 entries are 263
distinct ids. *No
comparison* is where either verdict is *contested or unclear* and the reader recorded no
match.

The seventeen disagreements:

| reader | id | section and case | kind | the author's verdict | the formal verdict |
|---|---|---|---|---|---|
| A | `resentment-real-injustice` | 2.2.1, resentment over past injustices | K2 | manipulates | contested or unclear |
| A | `jo-allen-not-bluffing` | 2.2.7 Emotional Blackmail (paradigm); 3.9, 3.10; also tantrums, sulking, silent treatment | cannot say | manipulates | contested or unclear |
| A | `arguing-to-convince-wears-down` | 2.2.8, Baron's contrast | K4 | not manipulation | loose sense only |
| A | `conditional-compliments-mundane` | 2.2.13, mundane examples and Recker | K3 | manipulates | contested or unclear |
| A | `chair-conditional-flattery` | 2.2.13 Conditional Flattery (paradigm) | cannot say | manipulates | contested or unclear |
| A | `teacher-feigns-excitement` | 3.2 | K1 | not manipulation | manipulates |
| A | `subliminal-hypnosis` | 3.5, subliminal advertising and hypnosis as popularly imagined | cannot say | manipulates | contested or unclear |
| A | `professor-conditioned` | 3.5, students condition a professor | cannot say | manipulates | not manipulation |
| A | `lucrative-suicide` | 3.5 Lucrative Suicide (Gorin) | none | manipulates | not manipulation |
| A | `announced-nagging-phone` | 3.6, teen nags for a phone and says so | cannot say | manipulates | contested or unclear |
| A | `open-peer-pressure-smoking` | 3.6 | cannot say | manipulates | contested or unclear |
| A | `physician-displeasure` | 3.10 (Faden, Beauchamp and King) | cannot say | manipulates | contested or unclear |
| A | `wont-be-your-friend` | 3.10 (Baron) | cannot say | manipulates | contested or unclear |
| B | `baron-nervous-requestee` | 5.8 (Baron's example) | K4 | not manipulation | loose sense only |
| C | `rigged-coin` | 10.7, rigged tie-breaking coin | cannot say | not manipulation | contested or unclear |
| C | `snake-warning-sign` | 11.2, snake warning sign | K2 | not manipulation | loose sense only |
| C | `social-media-engagement` | 11.8, social media design | K4 | manipulates | loose sense only |

Thirteen are from chapters 2 and 3. In eight the author counts the case and the formal
statement finds no estimate off and no choice stated to be against her own judgment:
pressure through a real cost (emotional blackmail without a bluff, announced nagging, open
peer pressure, a physician's displeasure, a conditional threat), conditional flattery
twice, and resentment over a real injustice. Three are influence with no mistake on the
list (hypnosis, conditioning, a rational argument given to a man with a fatal belief). Four
turn on the loose sense, which the formal statement grants wherever a caused mistake
changes behaviour: three the author does not count, and the design of a social-media
platform, which he does. One is a teacher who feigns excitement, where the formal statement
convicts and the author does not, and one a rigged tie-breaking coin.

**What the run can show.** Where a formal reading of the Mistake Account, applied by one
reader per part, gives the verdict that reader took to be the author's, and the kinds of
case where the estimator vocabulary strains: 78 of 266 entries fit it with no note, 45 of
them cases with no mistake. **What it cannot.** That the readers' paraphrases, encodings or
attributions of the author's verdict are right: each part had one reader, nothing was coded
twice, and no person has checked any entry against the book. Agreement between the formal
verdict and the author's is agreement between two judgments of the same reader. The count
is not a test of the account of `MISTAKES_ACCOUNT.md`, which keeps Noggle's definition and
adds a property the readers were not given.
