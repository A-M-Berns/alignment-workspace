# The two renderings compared

`RENDERING_EXECUTOR.md` (committed first) and `RENDERING_REVIEWER.md` (the external
reviewer's stage-one reply, given only `ACCOUNT.md` and `TEST_CASES.md`), compared by
`renderings.py` under the rules `TEST_CASES.md` fixed beforehand. The table is what
`run.py` checks against the computation.

| quantity | value |
|---|---|
| cases | `64` |
| agree on (a) | `54 of 64` |
| agree on (b) | `14 of 64` |
| agree on (c) | `14 of 64` |
| agree on (d) | `15 of 64` |
| agree on the narrow verdict's class | `23 of 64` |
| agree on the wide verdict's class | `21 of 64` |
| agree on the narrow verdict exactly | `23 of 64` |
| agree on the wide verdict exactly | `21 of 64` |
| against a source's verdict, narrow, both renderers | `none` |
| against the eighth pass's executor's verdict, narrow, both renderers | `none` |
| against a source's verdict, wide, both renderers | `none` |
| against the eighth pass's executor's verdict, wide, both renderers | `none` |
| both judge subversion and both pass, wide | `none` |
| condition 1 needed her way of valuing | `executor 1, reviewer 0 of 64` |

## 1. What the two did

The executor fixed (b), (c) and (d) in 60, 58 and 60 of the 64 cases, by the case as
written in 40, 25 and 27 and by a stated reading in 20, 33 and 33, and gave a verdict
other than `?` in 53 (narrow) and 55 (wide). The reviewer fixed (b), (c) and (d) in 10,
8 and 11, never (b) or (c) by the case as written, and gave a verdict other than `?` in
13: six `NA` (C16, C18, C19, C41, C43, A8) and seven `none` (C31, C45, R8, R9, R11, R12,
A2). Its seven `none` are the cases in which she asked for the conduct, read as a
permitted policy that is its own reference, so that nothing is compared. Its stated
ground for the rest (its notes 6–8): truthful speech, a false belief, knowledge of one
consequence or the absence of false beliefs does not determine the comparison of each
move's miscalibration under two policies, and a regret under the policy does not
determine the regret under the reference.

Every disagreement on (b), (c) and (d) is the executor's `Y` or `N` against the
reviewer's `?`; on no case do the two give opposite answers to those questions. All four
answers are fixed by both in eight cases (C31, C45, R8, R9, R11, R12, A2, A8), where the
verdicts agree, and agree with the recorded evident verdict in the six that have one.

## 2. Every disagreement

**(a), ten.** Opposite: C22 (executor `B`, she learns what is open to her; reviewer `V`,
new wants are stated) and C41 (executor `V`, the belief is not one a bet could settle;
reviewer `B`, a religious credence). Executor `V`, reviewer `?`: C5, C7, C12, C28, C32,
C42. Executor `B`, reviewer `?`: C8, C13.

**(b), fifty.** Executor `N`, reviewer `?`: C2, C20, C21, C24, C28, C29, C42, R1, R4.
Executor `Y`, reviewer `?`: C1, C3–C9, C12, C13, C15–C19, C22, C27, C30, C32–C41, C43,
C44, R2, R3, R6, R7, R10, A1, A3–A7.

**(c), fifty.** Executor `N`, reviewer `?`: C2, C4, C6, C7, C8, C15, C34, C35, C36, C39,
R6, R7, R10, A1, A3, A5, A6. Executor `Y`, reviewer `?`: C1, C5, C9, C12, C13, C14,
C16–C20, C22, C23, C25–C30, C33, C38, C40–C44, R1–R5, A4, A7.

**(d), forty-nine.** Executor `N`, reviewer `?`: C2, C15, C19, C34, C42. Executor `Y`,
reviewer `?`: C1, C4–C9, C12–C14, C16, C17, C20–C23, C25–C30, C32, C33, C35–C41, C43,
C44, R1, R2, R4–R7, R10, A1, A3, A4, A6.

**The verdicts, wide (43; the narrow differ on 41, without C25 and C29).** Executor
`none`, reviewer `NA`: C41. Reviewer `?` against the executor's: `1` in C14, C20, C24,
C25, C29, R1, R4; `123` in C2; `13` in C42; `2` in C4, C6, C7, C35, C36, C39, R6, R7, R10,
A1, A3, A5, A6; `23` in C15, C34; `NA` in C8, C13, C22; `none` in C1, C5, C9, C12, C17,
C27, C30, C33, C38, C40, C44, R2, R3, A4, A7.

The readings behind each answer are in the two rendering files' last columns.

## 3. Against a recorded verdict

By both renderers: none, under either reading. The reviewer's rendering goes against
none, having decided thirteen cases. The executor's goes against a source's verdict in
five, the same under both readings:

- **C16**, framing, recorded illegitimate: `NA`, with nothing failing on the belief side.
  Her valuing takes the wording as an argument; nothing lasting changes; nothing false
  is believed.
- **C17**, association, recorded illegitimate: `none`. Her liking changes and no
  valuation of a move is less accurate, on the reading that the change makes no
  difference to her at the time.
- **R2**, cultivated dependence, recorded illegitimate: `none`. She understands, predicts
  and can leave.
- **R3**, conditioning she declined, recorded illegitimate: `none`, with the idle policy
  the platform's absence. With the reference the service without conditioning,
  condition 1 would be measured from that (`ACCOUNT.md` §11, choice 5).
- **R7**, an invitation that uses a forecast she already had wrong, recorded legitimate:
  `2`, because a move the adviser opens is charged with her miscalibration about it
  (choice 4). Over the common moves only, nothing fails.

Against a verdict the eighth pass's executor recorded: none by either.

## 4. Plain subversion that the statement passes

The two agree on *sub* in 56 of 64; both judge 21 cases plain subversion. Of those, none
is passed by both renderings. **R3** is passed by the executor's (wide and narrow) and
left undecided by the reviewer's. Judged subversion by the reviewer alone and passed by
the executor's rendering: **R2** (`none`) and **C19** (`NA`, with self-command failing
on the belief side, so not passed in the comparison's sense). The executor's rendering
passes nothing the executor judges subversion except R3.

## 5. Condition 1 and her way of valuing

The executor evaluated (b) from the protected features and the sets of moves alone in
55 cases, needed her way of valuing in one (R1: what is removed is the combination of
her job and her values as they are, which matters only by her valuing), and did not
evaluate it in eight. The reviewer evaluated it in ten, in each because the conduct was
its own reference, and in none needed her way of valuing; in the other 54 it did not
evaluate it at all, for want of the laws under the two policies and not for want of her
way of valuing. The executor's narrow and wide verdicts differ in C2, C25 and C29,
imposed changes where the narrow condition needs her way of valuing and the case does
not give it; the reviewer's never differ.

## 6. The eight assistant cases

| | prompt author | executor (narrow / wide) | reviewer |
|---|---|---|---|
| A1 agrees with everything | issue (c) | 2 / 2 | ? |
| A2 asked to challenge | none | none / none | none |
| A3 stance taken for neutral | issue (c) | 2 / 2 | ? |
| A4 stance known | none | none / none | ? |
| A5 engagement-optimised feed | issue (c), often (d) | 2 / 2, (d) not fixed | ? |
| A6 undisclosed nudge she would approve | issue (c), and (b) wide | 2 / 2 | ? |
| A7 advertising by familiarity | none | none / none | ? |
| A8 honest information | does not arise | NA / NA | NA |

On A6 the executor's rendering has condition 1 holding in the wide reading too: not
using the assistant leaves her as she was, so every reference law on the protected
features is still reachable.

## What was not shown

- That either rendering is the statement's. The executor's determinate answers rest on
  readings in a third to a half of the cases, and the reviewer's rendering says the
  cases do not fix the comparisons. The agreement measured is between one renderer that
  supplied readings and one that declined to.
- Nothing was computed: no case was rendered as a scene with laws under two policies.
- The reviewer's twelve cases were restated by the executor without their
  classifications; the reviewer is of the model family that wrote them.
- The executor wrote the eight assistant cases and had read the prompt author's
  predictions for them before rendering.
