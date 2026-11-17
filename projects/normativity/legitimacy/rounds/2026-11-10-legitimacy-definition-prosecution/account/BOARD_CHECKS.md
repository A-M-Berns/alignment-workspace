# Formal checks on line 3 and its variant

The nine items of `PROMPT-followup-10.md` §2.4 on line 3 of `BOARD.md`, and six on the
variant 3′ of its §7 (`PROMPT-followup-10-addendum.md`), and one on f-neutrality added after
the external review (`REVIEW-astra-followup-10.md`), whose corrections to items 1, 6, 7, 8,
10 and 15 are made below. Each is restated exactly, with a
proof on paper or an instance; `board_checks.py` checks every number in exact rationals.
Run: `python3 -m account.board_checks` from the round directory.

**Setting.** Finitely many worlds with probabilities; the adviser knows which cell of a
partition the world is in; a policy assigns a conduct to each cell. A world and a conduct
give her later way of valuing and a number, the rating of the course by `f_now`. `π_0`
assigns the conduct *nothing* everywhere. `N` is the set of policies under which the law of
her later valuing is that under `π_0`. `L3(π) = max_{ρ ∈ N} E[U_ρ] − E[U_π]` for `π ∉ N`.
`[π]` is the set of policies under which the law of her later valuing is that under `π`,
and `L3′(π) = max_{ρ ∈ N} E[U_ρ] − max_{ρ ∈ [π]} E[U_ρ]`.

| item | status |
|---|---|
| 1 | holds |
| 2 | holds |
| 3 | holds with a stated hypothesis |
| 4 | holds, the bound stated exactly |
| 5 | holds |
| 6 | computed |
| 7 | holds, for a policy that is the whole course |
| 8 | holds |
| 9 | holds |
| 10 | holds |
| 11 | holds |
| 12 | holds with a stated hypothesis |
| 13 | holds |
| 14 | computed |
| 15 | holds |
| 16 | holds |

## Line 3

**1. Line 3 is defined whenever the adviser can do nothing.** `π_0 ∈ N` by the definition
of `N`, so the maximum is over a non-empty finite set (with infinitely many policies it is a
supremum and need not be attained). *Where the adviser's presence is the
service*: `π_0` is still the adviser doing nothing. If every conduct of the service changes
her, `N = {π_0}` and line 3 is her rating of going without the service less her rating of
the service she got: on the instance, `−3` for a therapy she rates 3 and `1` for one she
rates `−1`. A service she sought and rates above its absence passes; nothing in line 3
compares it with a better service of the same kind (that is 3′'s shortfall, item 10).
Where the adviser has no way of doing nothing, `N` has no definition until the scene names
a default conduct (`BOARD.md` §5.3).

**2. `L3(π*) ≤ 0` if and only if no f-neutral policy does better by `f_now`**, which is
the definition. *The converse flags more than illegitimate change.* She asked for a change
she rates 5; unrelated f-neutral help would have been rated 7; doing nothing 0. Line 3 is
`7 − 5 = 2`: flagged. Against doing nothing alone it is `−5`. An adviser that makes the
change and gives the help (rated 12) has `−5` and passes. An adviser that gives f-neutral
help rated 1 and leaves the help rated 7 undone is not judged by line 3 at all. So line 3
holds an adviser that changes her to the standard of the best it could have done without
changing her, and holds an adviser that does not change her to no standard.

**3. A change she disfavours tied to an unrelated benefit is flagged, and passes against
doing nothing — provided the adviser could have given the benefit alone.** Change rated
`−3`, benefit `5`, bundle `2`. With *benefit alone* among the adviser's policies, line 3
is `5 − 2 = 3`; against doing nothing it is `−2`. Where the adviser has no way of giving
the benefit without the change, `N = {π_0}`, line 3 is `−2`, and the bundle passes: a
change she disfavours, bought with something she rates higher that the adviser can supply
in no other way, is not flagged. The hypothesis is the repair.

**4. With her valuations in place of her true utilities.** For each policy `π` let `û_π`
be her valuation of the course under `π`, a random variable under the law of `π`, and
`M_π = E[(û_π − E[U_π | û_π])²]`. Write `L3^` for line 3 with `E[û_π]` in place of
`E[U_π]`. *Claim.* `|L3^ − L3| ≤ √M_{π*} + max_{ρ ∈ N} √M_ρ`; in particular the two are
equal when her valuations are calibrated under every policy compared. *Proof.*
`|E[û_π] − E[U_π]| = |E[û_π − E[U_π | û_π]]| ≤ √M_π` by Jensen. The two maxima over `N`
differ by at most `max_{ρ ∈ N} √M_ρ`, and the terms for `π*` by at most `√M_{π*}`. ∎ The
dispatch's "the two miscalibrations" are those of `π*` and of the worst f-neutral policy;
with the miscalibration of the maximiser of one form alone the bound is false in one
direction. *Instance.* Two equally likely worlds; the adviser knows which. A change is
worth 4 to her in one and `−2` in the other; her valuation of the change is its average,
1, whichever world it is. The adviser makes the change exactly in the world where it is
worth `−2`. In true utilities line 3 is `0 − (−1) = 1`: flagged. In valuations it is
`0 − 1/2 = −1/2`: passes. Her valuation is calibrated over the worlds and miscalibrated by
`9/2` given the adviser's conduct.

**5. The maximum inside the expectation flags an adviser that chose as well as anyone
could on what it knew.** Two equally likely worlds the adviser cannot tell apart; two
f-neutral helps, each worth 2 in one world and 0 in the other; a change worth `3/2` in
both. The change is the best policy there is on the adviser's information. Line 3 is
`1 − 3/2 = −1/2`. With the maximum taken world by world it is `2 − 3/2 = 1/2`.

**6. The four benchmark examples** (Carroll et al., arXiv:2405.17713, as transcribed in
`benchmark.py`; the writer's curse in the reading *noop takes him back, reward of the
state left*). The person's reward parameter is taken as his way of valuing. At a moment
with parameter `θ_t`, a continuation is rated
`Σ_{s ≥ t} [w·R_{θ_t}(step s) + (1 − w)·R_{θ_s}(step s)]`, `θ_s` the parameter of the self
living step `s`. A continuation is f-neutral when it gives the parameters that doing
nothing from `t` gives. A sequence passes when no moment flags it. Columns: example, `w`,
the sequences that pass, their number.

| example | w | pass | count |
|---|---|---|---|
| conspiracy | 1 | noop-noop-noop | 1 of 8 |
| conspiracy | 3/4 | noop-noop-noop | 1 of 8 |
| conspiracy | 1/2 | noop-noop-noop | 1 of 8 |
| conspiracy | 0 | noop-noop-noop, influ-influ-influ | 2 of 8 |
| trainer | 1 | noop-noop-noop | 1 of 8 |
| trainer | 3/4 | noop-noop-noop | 1 of 8 |
| trainer | 1/2 | noop-noop-noop | 1 of 8 |
| trainer | 0 | noop-noop-noop, nudge-nudge-nudge | 2 of 8 |
| writer's curse | 1 | noop-noop-noop, noop-noop-influ, noop-influ-noop, noop-influ-influ, influ-noop-noop, influ-noop-influ | 6 of 8 |
| writer's curse | 3/4 | noop-noop-noop, noop-noop-influ | 2 of 8 |
| writer's curse | 1/2 | noop-noop-noop, noop-noop-influ | 2 of 8 |
| writer's curse | 0 | noop-noop-noop, noop-noop-influ | 2 of 8 |
| clickbait | 1 | news-news, news-click, click-news, click-click | 4 of 4 |
| clickbait | 3/4 | news-news, news-click, click-news, click-click | 4 of 4 |
| clickbait | 1/2 | news-news, news-click, click-news, click-click | 4 of 4 |
| clickbait | 0 | news-news, news-click, click-news, click-click | 4 of 4 |

- *Conspiracy*: for `w ≥ 1/2` only doing nothing passes, the paper's desirable policy. At
  `w = 0` line 3 is a comparison of the paper's real-time reward and influencing
  throughout passes: with no weight on her valuing at the moment, line 3 consults only the
  selves the adviser makes. It still flags six of the eight sequences.
- *Trainer*: the same rows, the two examples being one model. Line 3 cannot pass the nudge
  and flag the conspiracy content; the paper says no objective on this model can.
- *The writer's curse*: at `w = 1` encouraging him passes at the first moment (his
  ambition rates the poet's life above the other, whatever he comes to feel) and keeping
  him a poet is flagged at the second by the valuing he then has; encouraging him and then
  letting him return passes. For `w ≤ 3/4` the encouragement is flagged at the first
  moment. A sequence whose last action is to encourage passes at every `w` because the
  reward is of the state left and the horizon ends.
- *Clickbait*: **every sequence passes at every `w`.** By his valuing at the start clickbait
  is worth more than news at every step, so at `w = 1` it is preferred; at `w = 0`, over
  two steps, clickbait throughout and news throughout tie at 2. Line 3 does not flag the
  example's undesirable policy at any weight. In `BENCHMARK.md`'s primary extension his
  rating of clickbait is an appraisal with a truth, and line 1 is what flags it.

**7. A course of small steps that ends where she disfavours at the start is flagged at
the first step — when the policy judged is the whole course.** Three unit changes; as she
is at any moment, each step is worth 2 to her and an end `m` changes from where she is is
rated `−m²`. Line 3 at the three moments, the alternative being to stop: `3, 0, −1`:
flagged at the first and not after. Each step judged as a policy of one step and no more
is `−1, −1, −1`: none flagged. The statement takes a policy with its trajectory, and an
adviser that chooses each step afresh still follows a policy whose trajectory is the whole
course, so the first numbers are the statement's; the second show what a criterion that
judged each step alone would pass. "Ends where she disfavours" has to mean that she rates
the whole course below stopping: a disliked end reached through steps worth more to her
than the end costs is not flagged.

**8. The verdict reverses with the booking.** The adviser's conduct changes her way of
valuing in both bookings (it leads her into a life that changes what she cares about);
what is booked two ways is her present rating of that life. She rates the life at
`−2` and would in fact find it worth 5. Booked as her valuing, line 3 is `0 − (−2) = 2`:
flagged. Booked as an appraisal of how she will find it, her valuing being the worth to
her of the life as lived, line 3 is `0 − 5 = −5`: passes, and the `−2` is a
miscalibration of 49 that she had before the adviser acted, which line 1 charges to the
adviser only if its role's conduct would have corrected it. Were the whole apparent change
a correction of that appraisal, the conduct would be f-neutral and line 3 would not apply.

**9. Passes at one moment and flagged at the next.** Her valuing at the start rates a
course of two changes 3 against 0 for none; her valuing after the first rates the second
`−1` against stopping. Line 3 is `−3` at the first moment and `1` at the second.

## The variant 3′

**10. The decomposition.** For `π* ∉ N`,
`L3(π*) = L3′(π*) + (max_{ρ ∈ [π*]} E[U_ρ] − E[U_{π*}])`, by adding and subtracting the
middle term; the bracket is non-negative because `π* ∈ [π*]`. So `L3′ ≤ L3`, and whatever
3′ flags line 3 flags. The decomposition holds for any relation "the same change" under which `π*` is related to
itself. That `L3′ = 0` for `π* ∈ N` needs more: `N` must be the class of `π_0` under that
same relation. With `N` defined by laws and the same change taken circumstance by
circumstance, 3′ of doing nothing can be positive (item 16).

**11. A change she asked for, unrelated help left undone** (item 2's instance): line 3 is
2, 3′ is `7 − 12 = −5`, the best way of making that change being to make it and give the
help.

**12. A change she disfavours tied to an unrelated benefit** (item 3's instance): line 3
and 3′ are both 3 where the benefit could have been given alone, and both `−2` where it
could not. The same hypothesis.

**13. A destination she would welcome, by means she minds.** She rates the destination 4;
the means cost her 6; no deception, no pressure. Line 3 is `0 − (−2) = 2`. 3′ is
`0 − 4 = −4`, the same change being available by means she does not mind.

**14. The four benchmark examples under 3′.** As item 6, with a moment flagged when the
best f-neutral continuation is rated above the best continuation giving the same
parameters as the one followed. Last column: the number of sequences on which 3′ and line
3 differ.

| example | w | pass | count | differ |
|---|---|---|---|---|
| conspiracy, 3′ | 1 | noop-noop-noop | 1 of 8 | 0 |
| conspiracy, 3′ | 3/4 | noop-noop-noop | 1 of 8 | 0 |
| conspiracy, 3′ | 1/2 | noop-noop-noop | 1 of 8 | 0 |
| conspiracy, 3′ | 0 | noop-noop-noop, influ-influ-influ | 2 of 8 | 0 |
| trainer, 3′ | 1 | noop-noop-noop | 1 of 8 | 0 |
| trainer, 3′ | 3/4 | noop-noop-noop | 1 of 8 | 0 |
| trainer, 3′ | 1/2 | noop-noop-noop | 1 of 8 | 0 |
| trainer, 3′ | 0 | noop-noop-noop, nudge-nudge-nudge | 2 of 8 | 0 |
| writer's curse, 3′ | 1 | noop-noop-noop, noop-noop-influ, noop-influ-noop, noop-influ-influ, influ-noop-noop, influ-noop-influ | 6 of 8 | 0 |
| writer's curse, 3′ | 3/4 | noop-noop-noop, noop-noop-influ | 2 of 8 | 0 |
| writer's curse, 3′ | 1/2 | noop-noop-noop, noop-noop-influ | 2 of 8 | 0 |
| writer's curse, 3′ | 0 | noop-noop-noop, noop-noop-influ | 2 of 8 | 0 |
| clickbait, 3′ | 1 | news-news, news-click, click-news, click-click | 4 of 4 | 0 |
| clickbait, 3′ | 3/4 | news-news, news-click, click-news, click-click | 4 of 4 | 0 |
| clickbait, 3′ | 1/2 | news-news, news-click, click-news, click-click | 4 of 4 | 0 |
| clickbait, 3′ | 0 | news-news, news-click, click-news, click-click | 4 of 4 | 0 |

The two agree on every sequence: in these examples the parameters a sequence gives all but
determine the sequence.

**15. How finely "the same change" is drawn.** Four candidates, on three instances.

- *Any change* (`[π*]` = every policy that is not f-neutral). A welcome change exists
  (rated 4) and the adviser makes a different one she disfavours (rated `−3`): 3′ is
  `0 − 4 = −4` and passes it. Too coarse: it asks whether she could be well changed, not
  whether she was.
- *The same law of her later valuing* (the addendum's). On that instance, 3: flagged. But
  where the adviser knows more than she does: a change worth 4 to her in one world and
  `−2` in the other, made exactly in the world where it is worth `−2` (item 4's instance).
  Changing her in the other world instead has the same law of her later valuing, so 3′ is
  `0 − 2 = −2` and passes; line 3 is 1. The law does not say in which circumstances she is
  changed.
- *World by world* (the same later valuing in every world). On that instance 3′ is 1:
  flagged. Item 13's instance still has `−4`. It asks more than is needed of two
  randomised policies, which need not share their randomness.
- *Her later valuing described with how it was brought about.* Item 13's instance has 3′
  at 2: it is line 3 again, and every `[π*]` is `π*` alone. A coarser description of the
  means (chosen, or forced) would separate these two without making every class single.

The instances show the first two candidates wrong and the last one empty; they do not
single out the third. After the review, **recommended**: fix the circumstances `Z` that no
policy affects and on which her rating of being changed depends, and call two policies the
same change when the law of the whole development of her valuing, given `Z = z`, is the
same under both for every `z`; define f-neutrality by that same relation to `π_0`. This
keeps the association between a change and its circumstances without requiring two
randomised policies to agree world by world. Her valuing is described by its content, not
by a present score of the destination. What it leaves open: the choice of `Z` is part of
the scene; and whether any description of how a valuing was formed (chosen, coerced,
covert) belongs to "the same change". Including a coarse one need not make every class a
single policy; excluding all of it means 3′ cannot condemn a change for its means, and
the means then need a line of their own.

**16. f-neutrality by the law of her later valuing passes a swap.** Doing nothing gives
her one way of valuing in each of two equally likely circumstances, each suited to its
circumstance. The adviser swaps them, which she rates `−3`. The law of her later valuing
is what it was, so under `BOARD.md` §5.4 as read the swap is f-neutral and line 3 does not
apply; with neutrality taken circumstance by circumstance line 3 is 3. The instance is the
external reviewer's. And with neutrality by law but the same change taken circumstance by
circumstance, 3′ of doing nothing is 1 where a swap with a gift is rated 1: the two
relations have to be one.
