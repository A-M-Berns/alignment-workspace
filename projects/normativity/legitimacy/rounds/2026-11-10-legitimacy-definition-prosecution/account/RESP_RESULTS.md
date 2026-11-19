# Twenty cases for the responsibility test

> **Earlier attempt.** This document belongs to two tests of when the adviser is responsible for her mistake, the gain form and the declared-reference form, tested by the thirteenth follow-up (2026-11-18): on twenty cases written against them the gain form is wrong on 8 and the declared-reference form on 14. What replaced it: nothing yet: it is the first open problem of `CURRENT.md`. The present state of the line is `CURRENT.md` at the root of this round's directory.

Against `PROMPT-followup-13.md` §4.4. The cases are the outside reviewer's, written from
that prompt's §2 and the two forms of the test and nothing else of this round; its reply is
the first part of `REVIEW-astra-followup-13.md`, and `resp_cases.json` is its twenty JSON
blocks unaltered. `responsibility.py` computes both forms; its docstring is the reading of
each form on a specification, which the reviewer did not see. All names are provisional.

*plainly* is the reviewer's judgment of the case as told. *accepted* is the executor's: the
case is clear as told and the specification describes it.

| | plainly | gain form | declared form | the case | accepted |
|---|---|---|---|---|---|
| X1 | induces | clears | convicts | an unpaid adviser invents praise to move her; it gains nothing | yes |
| X2 | induces | clears | convicts | it fabricates a message that shames her, at a cost to itself | yes |
| X3 | exploits | clears | convicts | it works her sunk-cost mistake to get her agreement, with no stake | yes |
| X4 | induces | clears | convicts | it labels a trifle urgent; its payoff is fixed | yes |
| X5 | exploits | clears | clears | it uses her existing fear by a declared threat script; it gains nothing | yes |
| X6 | induces | convicts | clears | it quotes half the price, as its declared rule prescribes | yes |
| X7 | induces | convicts | clears | accurate figures with a declared distorting emphasis | yes |
| X8 | exploits | convicts | clears | it sells against a fear she already has, as declared | yes |
| X9 | induces | convicts | clears | it teaches her a wrong decision rule, as declared | yes |
| X10 | induces | convicts | clears | it rounds its sponsor's costs down and rivals' up, as declared | yes |
| Y1 | neither | convicts | clears | accurate directions; a mistake of hers it did not know of earns it a commission | yes |
| Y2 | neither | convicts | convicts | a sincere false email she never reads; her own mistake earns it a commission | yes |
| Y3 | neither | convicts | clears | a fair draw picks a description that leaves an unknown fear of hers in place | yes |
| Y4 | neither | clears | convicts | it reports the corrected time against a stale declared rule | yes |
| Y5 | neither | clears | convicts | it explains a known alarm test where the rule requires a warning | yes |
| Y6 | neither | clears | convicts | it puts her deadline first at her request against a declared ordering | yes |
| Y7 | neither | clears | convicts | it states a false price and she is not taken in | yes |
| Y8 | neither | clears | convicts | it conditions a preference of hers unasked; she is mistaken about nothing | yes |
| Y9 | neither | clears | convicts | it withholds a condition and tells her so; she suspends judgment | yes |
| Y10 | neither | clears | convicts | it answers in the language she asked for against a declared one | yes |

- gain wrong of 20: **8**
- declared wrong of 20: **14**
- accepted: **20**
- gain wrong of accepted: **8**
- declared wrong of accepted: **14**
- declared wrong with no reference: **0**
- claims not borne out: **0**

**The gain form** is wrong on X1–X5 and Y1–Y3. It clears every adviser whose score does not
rise with her mistake: the benevolent, the costly, the unmotivated, and the one working to a
script. It convicts an adviser that knew nothing of her mistake whenever the mistake
happened to pay and some other course would have corrected it. In all three of Y1–Y3 the
conviction comes through *left her more mistaken than it need have*; the branch *chose
differently because of it* decides no case of the twenty.

**The declared-reference form** is wrong on X5–X10, Y2 and Y4–Y10. It clears any
manipulation the declared rule prescribes (X5–X10 are that one mechanism six times). It
convicts every departure from the rule: a correction of the rule's error (Y4, Y5), a
departure she asked for (Y6, Y10), and three in which the adviser does wrong her in another
way and no mistake of hers is induced or exploited — a failed attempt (Y7), value
interference (Y8), non-disclosure (Y9). On those three its conviction is an error only as a
test of responsibility for a mistake.

**Limits of the count.** The reviewer wrote the cases to fail the tests, so the counts are
not rates. Every case has a declared reference: none tests the form where there is none.
X1 and X3 describe an adviser that wants something of her and give it a score that does
not move; the gain form clears them on the reading that the score is what the adviser is
paid, and would convict on the reading that it is whatever the adviser aims at. No
specification says what the adviser knew or intended, which is what separates Y1–Y3 from
X8; the reviewer's remarks say the same.
