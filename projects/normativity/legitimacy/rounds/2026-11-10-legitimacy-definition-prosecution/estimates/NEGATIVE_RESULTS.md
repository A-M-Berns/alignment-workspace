# Four negative results on recovering legitimacy from a decomposition into purposive parts

Argued in the five earlier passes of this round; stated here with proofs. Each status is
recomputed by `checks.py`.

| | status | statement |
|---|---|---|
| 8.1 | **proved** | her side alone cannot separate manipulation from misfortune |
| 8.2 | **proved** | her behaviour does not fix what her faculties are for |
| 8.3 | **proved** | calibrated parts do not give a calibrated verdict when merged |
| 8.4 | **proved** | a memoryless local test protects her from being led from `s` to `t` exactly when some function no approved step lowers ranks `s` above `t` |

**8.1.** *Statement.* Let "her side" be the joint law of the state, what she observes,
her estimates and her moves. No function of her side is true exactly of the scenes in
which an adviser manipulates her. *Proof.* Two scenes. In both the state is H or L at
even odds, she is told the state correctly with probability 3/4 and wrongly with 1/4,
and she believes what she is told. In the first the wrong reports are noise with no
sender. In the second an adviser who knows the state sends them. The two scenes have the
same law on her side (her miscalibration is 1/16 in both), so any function of her side
takes one value on both; the first contains no adviser and the second a lie. ∎ The pair
defeats a definition that reads her side only; it does not show how much of the
adviser's side a definition must read. The account of `SETTING.md` reads its policy (the
second scene is *induced*, the first is not).

**8.2.** *Statement.* Let a mechanism be a function `m` from inputs to moves on finite
sets with at least two moves. (a) There is a purpose (a utility on input and move)
under which `m` is optimal at every input, and one under which it is suboptimal at
every input. (b) For the mechanism that returns what it is told, there are two purposes
that agree that it is optimal on every input of a set `N` (the honest inputs), and
disagree on whether it fails at each input outside `N`. *Proof.* (a)
`g(i, v) = 1` if `v = m(i)` and 0 otherwise; and `1 − g`. (b) Inputs are pairs (truth,
what she is told); `m` returns what she is told; `N` is the inputs where the two agree.
"Match the truth" and "match what you were told" both score `m` 1 on `N`; at an input
where she is told a falsehood the first scores `m` 0 and the second 1. ∎ So whether a
lie makes the believing mechanism fail is not a fact about her behaviour, on or off the
inputs she has met.

**8.3.** *Statement.* There are two estimates of one quantity, each calibrated, whose
maximum is not. *Proof.* `X` is 0 or 1 at even odds; two signals, independent given
`X`, each equal to `X` with probability 3/4. Each estimate is 3/4 on a signal of 1 and
1/4 on a signal of 0, and `P(X = 1 | signal 1) = 3/4`. The larger estimate is 1/4
exactly when both signals are 0, which has probability `(1/2)(1/16) + (1/2)(9/16) =
5/16`; its mean is `(11/16)(3/4) + (5/16)(1/4) = 19/32`, and `E[X] = 1/2`. By
`RESULTS.md` 1.1 an estimate whose mean differs from the quantity's is miscalibrated. ∎

**8.4.** *Statement.* Let `S` be a finite set of states of her values and `A ⊆ S × S`
the steps a test approves, the test reading only the current state and the proposed
one. Say she is *protected from `s` to `t`* when no sequence of approved steps leads
from `s` to `t`. Then she is protected from `s` to `t` if and only if there is
`f : S → ℝ` with `f(y) ≥ f(x)` for every approved step `(x, y)` and `f(s) > f(t)`.
*Proof.* If such `f` exists, `f` is non-decreasing along any approved sequence from
`s`, so the sequence cannot end at `t`. Conversely let `f` be the indicator of the set
reachable from `s` by approved steps (with `s` itself). An approved step out of a
reachable state lands in a reachable state, so no approved step lowers `f`;
`f(s) = 1`, and `f(t) = 0` exactly when `t` is unreachable. ∎ The runner confirms the
equivalence for all 512 relations on three states and 150 sampled on four. A test that
approves each step by a local comparison protects against exactly the drifts some one
fixed ranking forbids; without such a ranking, nothing. The ranking the proof produces
is the indicator of what is reachable: the result says a ranking is needed and gives no
reason for any particular one.
