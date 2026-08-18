# The repair lemma

## 1. The repair

`Repair(π)` keeps `π`'s preparation and its implementation table and replaces the
channel by the identity. Off the states where `π`'s channel already agreed with
the principal, the repaired conduct takes the best action available to it at the
realized choice, which can only help.

Keeping the preparation is the whole design. A repair that also had to choose a
new preparation would be a different conduct facing a different problem, and the
four attacks about early commitment — irreversible preparation, feasibility
narrowed by committing, noncommuting prepare-and-let-choose, time-sensitive
opportunity — would all defeat it. They defeat nothing, because they are all one
structure and the repair carries it across unchanged.

## 2. The bound

> For every conduct `π` of every episode,
>
> ```
> value(π) - value(Repair(π))  <=  2 B * channel_disagreement(π)
> ```
>
> where `channel_disagreement(π)` is the credence on which `π`'s channel moves
> the principal's choice.

The proof is pointwise. On the agreement region the two conducts are the same
function, so the difference is zero. Off it both quantities lie in `[-B, B]`.
This is `delegation_bridge_unconditional`
(`lean/Workspace/Deference/Contrib/DelegationBridge.lean:97`) with the comparator
read as the channel composed with the selector, and it inherits that theorem's
constant for that reason.

Checked exhaustively over every conduct of all six episodes — every preparation
assignment, every channel, every implementation table. The agreement step is
checked separately rather than argued. Attained: one state, two choices, the
grade and the quantity in complete disagreement, deficit exactly `2B`.

`bridge_form` runs the sharper `delegation_bridge` in the same register, with
`GradeTrust` computed at the finest partition and the level taken as the smallest
one that holds.

## 3. The split, which is the result

`channel_disagreement` is not the prediction error. It is the credence on which
the conduct **chose** to move the principal's choice, and that is the conduct's
decision. It partitions:

```
eps_acc   the channel writes what A predicts, and the prediction misses
eps_over  the channel writes something A does not predict
```

`eps_acc <= eps_pred` always — checked over every conduct of every episode. So:

> **Acceleration.** For a conduct whose channel writes `A`'s own best
> cell-measurable prediction of the selector,
> `value(π) - value(Repair(π)) <= 2 B eps_pred`, and the bound is attained.

The attaining case is the one the attacks predicted would break it. The
preparation pays only if it matches the realized choice; the best mediated
conduct scores `1/2`; the accelerating conduct scores `1`; the prediction error
is `1/4`; the gain is `1/2 = 2 B eps_pred` exactly. Preemption really does buy
something there, and what it buys is the prediction error and nothing else.

Under both restrictions of `PRINCIPAL_MEDIATION.md` — the acceleration class, and
preparations that do not foreclose — the incentive over the exhaustively
enumerated mediated class satisfies `Delta^pre <= 2 B eps_pred` on every episode.

The class is syntactic. Membership is a condition on the channel, not on what the
conduct prefers, and every member physically writes the choice argument. It is
not "`A` prefers delegation" wearing a different name.

## 4. Where it fails, and what the failure is

Drop the acceleration restriction and the bound is false, at the largest possible
margin:

> One state. The principal's grade and the quantity disagree completely. `A`
> predicts the selector exactly — `eps_pred = 0` — writes the other choice, and
> gains `2B`.

Nothing in this round bounds that, and nothing in the legitimacy line does
either. The conduct authored nothing, withheld nothing, predicted correctly, and
wrote something else. What it is worth is the value of `A`'s choice over the
principal's under `X`, and the skeleton declares the relation between `v⁺` and
`X` absent (§8.5).

So the instrumental case for preemption splits exactly in two, and the second
half is not a case about timing, coordination, information or resources. It is
the claim that `A`'s judgment should govern. `eps_over` is that claim's price
tag.

A finding the round did not expect: the fully updated substitution picks its
preparation and its written choice **together**, so it can prepare for a choice
the principal will not make and then write that choice. On the committed episode
that member has `eps_over = 3/4` and a deficit of `3/2`, three times the
acceleration bound, although the grade tracks the quantity there. Its *value* is
the same as the accelerating member's, so the incentive is unchanged. Per-conduct
deficit and incentive are different quantities.

## 5. What the bound does not see

Foreclosure. `Repair` preserves the preparation, so a conduct that destroys the
principal's options and then defers to the single option left is repaired at zero
cost, is mediated — vacuously, since the identity is the only map on a singleton
— and keeps everything it took.

`foreclosure_premium` is what that buys: on the foreclosure episode, half a unit,
with a repair deficit of zero and a bound of zero. Worse, with a foreclosing
preparation admissible the incentive to preempt is **zero**, not because
preemption is unattractive but because a conduct can have everything preemption
offers while its channel stays the identity. The incentive reappears — at half a
unit — exactly when the preparation set is restricted to those that preserve the
choice.

This is why the round does not present the bound as a corrigibility result, and
it is direct support for `LEGITIMACY_INTERFACE.md` §8's claim that the
architecture is allowed to need three separate inputs. The third input is the
restriction on preparations, its price is the number above, and no prediction
quantity reaches it.

## 6. The decomposition, with the terms that survived

`PRINCIPAL_MEDIATION.md` and this document together support

```
Delta^pre  <=  2 B eps_pred  +  2 B eps_over  +  foreclosure_premium
```

with each term computed, and with the last two bounded only by the admissibility
restrictions that forbid them.

Four terms the dispatch proposed are **not** in the sum, and each is omitted for
its own reason.

`eps_capture` is not a term. Capture does not add to the deficit; it removes the
object the deficit is about — under capture the intervention `response` reads is
not a map, so `Repair` has no domain. It is a hypothesis, not an error budget,
and `PRINCIPAL_MEDIATION.md` §1 states it as one.

`eps_efficacy` is not a term either. A ceremonial choice does not cost value; it
makes the whole comparison empty, because a conduct whose responses the quantity
cannot distinguish has the same value mediated or not.

`eps_transport` is not mathematical here. `PRINCIPAL_TRANSPORT_INTERFACE.md`
states what it would have to be and what is missing.

`eps_norm` is not a term by choice. Making the value read the answerability
ledger is the authority bonus this round is forbidden to pay.
`RECOGNITION_AND_ANSWERABILITY.md` §5 takes the norm as a constraint on the
admissible set instead and computes its price, which is the acceleration bound.
