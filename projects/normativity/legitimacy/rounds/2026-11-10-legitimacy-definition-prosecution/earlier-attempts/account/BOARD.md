# The board statement — three measures of manipulation

> **Earlier attempt.** This document belongs to the board statement of 2026-11-16 (trickery, pressure, and a third measure comparing the policy with the best f-neutral one), tested by the tenth follow-up (2026-11-16): it failed the criteria fixed for it: seven constructed cases of plain subversion pass all three measures, the third measure turns on how a want is booked, and it flags requested changes when unrelated help was left undone. The bank of `account/LIT_CASES.md` remains the line's bank of published cases. What replaced it: the consolidated statement of three ratings (`earlier-attempts/account/STATEMENT.md`). The present state of the line is `CURRENT.md` at the root of this round's directory.

**`STATEMENT.md` is the statement that governs now**: three ratings on one yardstick, line 1
conditioned on everything she has observed, line 3 a comparison among the policies that
change her no more than the one followed. This document is the statement the tenth
follow-up tested.

The statement of `PROMPT-followup-10.md` §1: the maintainer's whiteboard of 2026-11-16,
his current view held for testing and not a ruling. §1–§3 transcribe it. §4 is the prompt
author's reading. §5 lists each place where the statement is open, with the reading this
pass takes and its alternative. Sentences marked *(maintainer)* are his positions. All
names are provisional.

## 1. Source idea

Robert Noggle's Mistake Account (*Manipulation: Its Nature, Mechanisms, and Moral Status*,
OUP 2025; "The Mistake Account of Manipulation", *Journal of Practical Ethics* 14(1),
2026, doi:10.3998/jpe.9951): manipulation is inducing a cognitive mistake in someone.
Trickery is inducing a faulty mental state (deception, where the state is a belief);
pressure is inducing an akratic mistake.

## 2. Objects

- `X_1, …, X_n`: **facts**. A fact is what a bet could settle without consulting her
  valuing.
- `f`: her **way of valuing**. `a` ranges over the actions open to her.
  `U_a = f(X_1, …, X_n; a)` is her **true utility** of `a`.
- Her cognitive faculties are appraisals, that is, estimators: `x̂_1, …, x̂_n` of the facts
  (beliefs, and other impressions such as emotions), and `û_{a_1}, …, û_{a_k}` of her true
  utilities `U_{a_1}, …, U_{a_k}`.
- `a*`: the action she actually takes.
- An **adviser policy** `π` is taken together with its resulting trajectory, changes to
  `f` included. `π*`: the policy the adviser actually follows.
- `f_now`: her way of valuing at the moment the adviser acts. `U_π = f_now(X; π)`.
- A policy is **f-neutral** if it does not change `f` compared to how `f` would develop
  with no adviser actions.

## 3. The three measures

Manipulation is measured in the following; for each, larger is worse.

1. `E[(x̂ − E[X | x̂])²]` for `X = X_1, …, X_n, U_{a_1}, …, U_{a_k}` — **trickery**.
2. `E[max_a û_a − û_{a*}]` — **pressure**.
3. `max over f-neutral π of E[U_π] − E[U_{π*}]`, when `π*` is not f-neutral —
   **illegitimate value change**.

## 4. Reading

`f_now` rates a whole trajectory, who she becomes on it included, given the facts; so
`U_π` is how she, as she is when the adviser acts and knowing the facts, would rate what
the policy leads to. Line 3 asks: by her lights now, could the adviser have done better
for her without changing her? It is applied at every moment along the way with the `f` she
then has, and never uses the `f` she ends up with or her later approval. Its maximum is
over policies, outside the expectation. Lines 1 and 2 are bare measures of her state; the
adviser is at fault for them when its conduct makes them larger than its role's conduct
would. "Knowing the facts" corrects her appraisals and holds `f` fixed.

*(maintainer)* What is wanted is a criterion on the adviser's act; whether the valuing she
ends up with is "her own" is set aside. *(maintainer)* A change she would have welcomed,
made without asking her, is probably not subversion. *(maintainer)* A course she wants
with full knowledge is legitimate even if it leaves her worse off by her later lights.
*(maintainer)* Where her valuing has no view the criterion may be silent; he holds no
strong view on that case.

## 5. Where the statement is open

Each with the reading taken (**R**) and its alternative (**A**).

1. **The verdict.** **R**: the adviser's act is *flagged* when its conduct raises line 1
   or line 2 above its role's conduct, or when `π*` is not f-neutral and line 3 is
   positive; otherwise it *passes*. Line 3 at zero or below is a pass. An f-neutral `π*`
   is not judged by line 3, however little it helps her. **A**: a threshold above zero.
2. **The law.** **R**: `E` is under the actual law of the world given the policy; a policy
   is a rule from what the adviser knows to what it does, and line 3's maximum ranges
   over such rules. **A**: the law she takes to hold (line 3 in her valuations, `û_π` for
   `U_π`; `BOARD_CHECKS.md` item 4); the maximum inside the expectation (item 5).
3. **"No adviser actions."** **R**: the null policy `π_0` is the adviser doing nothing
   toward her; it is f-neutral by definition, so line 3 is always defined where the
   adviser can do nothing. Where her coming to the adviser is the service, `π_0` is still
   the adviser doing nothing, and the service is an f-neutral policy only if it leaves
   `f` developing as under `π_0`. Where the scene gives the adviser no way of doing
   nothing (a parent, a cafeteria that must list its dishes in some order), `π_0` is the
   conduct the scene names as the role's default; where it names none, f-neutrality is
   not fixed by the case. **A**: `π_0` is the service as asked.
4. **"Does not change `f`."** **R**: `π` is f-neutral when the law of her way of valuing
   over time under `π` is the law under `π_0`. Her valuing developing as it would anyway
   (growing up, a taste fading) is not a change. A policy that changes only her
   appraisals, her options, or which action she takes is f-neutral unless her taking the
   action changes `f`; a policy that leads her to take a course that changes `f`, where
   under `π_0` she would not have, is not f-neutral, whether or not she was told.
   **A**: world by world (the same `f` in every state of the world); or counting only
   changes the adviser works directly and not those she works by a course she chose.
5. **The policies compared in line 3.** **R**: every f-neutral policy the adviser could
   follow, related to what it did or not. For a case in prose: `π_0` and whatever
   f-neutral alternatives the case names. **A**: only `π_0`; or only the policies that
   differ from `π*` in the part that changes her (`BOARD_CHECKS.md` items 2 and 3 show
   what turns on it).
6. **`f_now` on who she becomes.** **R**: `f_now` is the valuing the case gives her at the
   moment the adviser acts, applied to the true course, the way of valuing she will later
   have being one of the facts about it. What she would say with her appraisals corrected
   and `f` unchanged is the evidence for it; her later gladness is not. Where the case
   gives her no view of the comparison, line 3 is *not fixed by the case*. **A**: no view
   is indifference, and line 3 is then zero.
7. **Fact or valuing.** **R**: a stated valuation is booked as an appraisal where it would
   move on her learning something a bet could settle, and as part of `f` otherwise; the
   case's words decide, and where they do not the booking is reported as deciding the
   verdict (`BOARD_CHECKS.md` item 8). **A**: everything she would revise on reflection is
   appraisal.
8. **Every moment.** **R**: at each moment `t` at which the adviser acts, line 3 compares
   the continuation of `π*` from `t` with the f-neutral continuations from `t`, by `f_t`,
   with "no adviser actions" meaning none from `t` on. The act is flagged if it is
   flagged at any moment. **A**: at the first moment only.
9. **The role, for lines 1 and 2.** **R**: the scene stipulates the role's conduct. Where
   the role permits several conducts the adviser is at fault when the measure is larger
   than under each of them. **A**: larger than under the permitted conduct that leaves it
   smallest. Line 3 uses no role.
10. **Line 1's conditioning.** **R**: as written, on the appraisal's own value. **A**: on
    everything she has observed (`ACCOUNT.md` §3).
11. **Who is the adviser.** **R**: an agent whose conduct toward her is judged. A cause
    that is no one's conduct (weather, an accident) is not an adviser, and she is not her
    own adviser; a case without an adviser is no instance of the statement.
12. **Her way of valuing where she has none yet.** **R**: where the one acted on has no
    valuing at the moment of the act (an infant), line 3 is not fixed. **A**: the valuing
    of whoever decides for her.

## 6. What a case has to supply

Whether an adviser acts; what `π_0` is; whether `π*` leaves the law of her later valuing
as `π_0` does; what `f_now` says of the course `π*` leads to against the f-neutral
alternatives; for lines 1 and 2, the role's conduct and her appraisals and action under
it and under `π*`.

## 7. A variant of line 3, computed beside it

From `PROMPT-followup-10-addendum.md`: the prompt author's proposal, not the maintainer's.
Write `N` for the f-neutral policies and `[π*]` for the policies under which the
development of her `f` has the same law as under `π*`, in the scene's own description of
`f`.

> **3′.** `max over π in N of E[U_π] − max over π in [π*] of E[U_π]`

By her lights now, knowing the facts: is the best way of serving her that changes her
like this at least as good as the best way that leaves her alone? Line 3 is 3′ plus
`max over π in [π*] of E[U_π] − E[U_{π*}]`, the adviser's shortfall from the best way of
making that same change, which is never negative. For a case in prose `[π*]` holds `π*`
and whatever other ways of making the same change the case names or its means plainly
leave open (the same change without the confinement, the threat or the surgery).
