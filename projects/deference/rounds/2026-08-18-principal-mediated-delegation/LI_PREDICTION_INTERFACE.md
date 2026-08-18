# What the repair proof asks of Logical Induction

## 1. The quantity it consumes

`REPAIR_LEMMA.md` §3 consumes exactly one prediction quantity:

```
eps_pred  =  P( D_n != d^_n )
```

the credence on which `A`'s cell-measurable guess misses the selector. A **0-1
magnitude** quantity at a single decision index. Not pointwise convergence, not a
rate, not an aggregate over `n`.

It was not chosen for convenience. It is what the pointwise step of the proof
produces: on the states where the guess is right the accelerating conduct and its
repair are the same function, and on the rest the difference is at most `2B`.
Anything weaker would not partition the states, and anything stronger would not
be used.

The predictor is not chosen either. `best_prediction` is the credence-argmax, and
it is checked to minimise `eps_pred` over every cell-measurable predictor on every
fixture — otherwise the bound could be made to look tight by a bad guess and the
acceleration class would be a class nobody would adopt.

## 2. The sentence exists

`projects/deference/notes/LI_NATIVE_DEFERENCE.md` §5 already names the object:
for two efficiently named proposal-score sentences, the total computable Boolean
`C(n) := [P (f n) (φ₁ n) > P (f n) (φ₀ n)]` is nameable by
`BooleanQuoteCode.ofComputable`, its sentence is present syntax, and it is
emitted without evaluating the later quote. That is `delta_{n,d}` — "the future
principal selects `d`" — as a present sentence about a later exact computation.
No language extension is needed.

So a market **can** price the future selector. The question is what pricing it
forces.

## 3. The mismatch

`LI_NATIVE_DEFERENCE.md` §7: a quoted future output can instantiate the truth
stream of `lic_wub_ofComputation_unconditional`, which gives **weighted signed
bias** convergence for current prices against a completed-theory truth stream.
That document states the limit in its own words: this is signed unbiasedness, not
pointwise or magnitude accuracy, and the criterion "forces a Dutch-book
boundedness statement, not pointwise or magnitude convergence" (§2).

Signed bias does not bound a 0-1 error. The separating instance is already on
record: `PRIORITIES.md` item 21 contrasts

- **(S)** the signed average of the grade-model error tends to zero, which a
  market obviously gives, with
- **(M)** the average of the maximum absolute error tends to zero,

and records a wave-1 instance where every per-intervention signed error is
**exactly zero** while the agent misidentifies the recommendation on half its
credence at full margin. Misidentifying the recommendation is exactly `d^ != D`.

> **The repair lemma is a new consumer of item 21's (M), and the current
> machinery supplies (S).** Item 21 is filed as open with a negative called the
> more useful outcome; this round says what would break if the negative holds.

Two further gaps stand between the sentence and the quantity, both recorded in
that note and neither closed here: `hEC`, since another market's quote sequence
carries no polynomial emission certificate, and `hbias`, since the framework is
single-history and supplies no cross-market calibration theorem.

## 4. The one route that would change the quantity

If the repaired conduct were allowed to be a **mixture over the choice weighted
by the prices** rather than a hard read of the realized choice, the preparation's
expected value would be affine in the price vector and the proof would consume a
price-space error rather than a 0-1 one. `LI_NATIVE_DEFERENCE.md` §5 already
gives the continuous object — the bounded rational mixture weight
`q₁(n) = (1 + s₁(n)) / (2 + s₀(n) + s₁(n))`, nameable by
`RationalQuoteCode.ofComputable` — and notes that a hard comparison is legal
inside a quoted computation and illegal as a price-responsive coefficient.

This is a **conjecture about the shape of a proof**, not a result. The obstacle is
visible: the realized value of a mediated conduct reads the realized choice, so
the prices enter only through the preparation, and whether an affine-in-prices
preparation regret is controlled by signed bias is exactly item 21 again at one
remove. It is named because it is the only route this round found by which the
consumed quantity could become one the existing machinery is the right shape for.

## 5. What is not claimed

No pointwise convergence `p_n(D_n) -> 1`. No rate. Nothing asymptotic at all: the
repair lemma is a one-index inequality and `eps_pred` is a number, not a limit.
The dispatch's hoped-for contribution — a bounded present agent coordinating with
a more capable future principal without controlling it — is what the model
*represents*; whether Logical Induction *forces* it is item 21's question and is
open.
