# Addendum to the tenth follow-up on PR #145 — a variant of line 3

Sent on 2026-11-16 while the tenth follow-up was running. The maintainer asked that the
strictness of line 3 be looked at; the variant below is the prompt author's proposal in
answer and is not yet the maintainer's. It adds one variant to be computed beside line 3
and one question for the review. It changes nothing else in the dispatch.

## 1. Why

Line 3 as dispatched compares what she got with the best the adviser could have done
while leaving her `f` alone. Write `N` for the f-neutral policies and `[π*]` for the
policies that change her `f` in the same way `π*` does. Then

`max_{π ∈ N} E[U_π] − E[U_{π*}]`
`  = ( max_{π ∈ N} E[U_π] − max_{π ∈ [π*]} E[U_π] ) + ( max_{π ∈ [π*]} E[U_π] − E[U_{π*}] )`.

The second bracket is how far the adviser fell short of the best way of making that same
change. It is never negative and has nothing to do with whether the change is one she
would choose. So line 3 flags a welcome, well-made change whenever the rest of the
adviser's conduct falls short by more than the change is worth to her.

## 2. The variant

> **3′.** `max over f-neutral π of E[U_π] − max over π in [π*] of E[U_π]`

In words: by her lights now, knowing the facts, is the best way of serving her that
changes her like this at least as good as the best way that leaves her alone? It is the
negative of what being changed this way is worth to her at best. When `π*` is f-neutral,
`[π*]` is the set of f-neutral policies and 3′ is zero, so no guard is needed.

`[π*]` needs a statement of when two policies change her `f` "in the same way". Take it as:
the development of her `f` has the same law under both, in the scene's own description of
`f`. Say where a verdict turns on how finely that description is drawn, and whether any
case makes `[π*]` contain `π*` alone, so that 3′ and line 3 coincide.

## 3. What to do with it

- In §2.3 and in the reviewer's first stage, record 3′ beside line 3 for every case in
  which an adviser acts: *raised*, *not raised*, *not fixed*, and where the two differ.
- In §2.4 add: the decomposition above, proved; an instance in which a change she asked
  for is flagged by line 3 and not by 3′ (unrelated help left undone); an instance in which
  a change she disfavours, tied to an unrelated benefit, is flagged by both; an instance in
  which a change whose destination she would welcome is brought about by means she minds,
  with no deception and no pressure, which line 3 flags and 3′ does not; and the four
  benchmark examples under 3′.
- Say what 3′ gives up: a harmful way of bringing about a change she would welcome is no
  longer a line-3 matter. List the cases of the bank in which that matters (the captive
  pianist is one), and say which other line, if any, catches each.
- Ask the reviewer, in its second stage: which of line 3 and 3′ is the better statement of
  illegitimate value change, and for a case that 3′ passes and that is plainly an
  illegitimate change of her values.

## 4. Success and failure

§4 of the dispatch is judged on the statement as dispatched. The variant is reported
beside it and decides nothing there. Where a judgment of §4 would come out differently
under 3′, say so.

New names introduced (provisional): 3′, `[π*]` ("the same change").
