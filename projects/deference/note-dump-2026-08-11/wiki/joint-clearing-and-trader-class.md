# Joint clearing and the trader class

*What the corrected faithful-acceleration work assumes when it lets two markets clear as one fixed point, what that buys, and why the one-way version costs almost nothing by comparison. Setting: $H\dashv\mathcal C_H$, $A\dashv\mathcal C_A$. Conventions: [[conventions-and-status-labels]]. Master map: [[index]].*

---

## 1. The assumption, as v3 states it

`fa-positive-results-corrected-v3.md` (A1), the **joint clearing** hypothesis:

> Each day $n$, *both* markets clear together, as one fixed point: a trader's day-$n$ coefficients may depend continuously on the day-$\le n$ prices of *both* markets, and its e.c. generator may hard-code any constants it can compute in time polynomial in $n$. Each side separately satisfies the logical induction criterion (no e.c. trader of this joint class exploits it).

Three things travel with it, all stated in v3 itself:

- **Existence is assumed, not cited.** The paper's construction produces one market per day by a Brouwer-style fixed point over strategies continuous in *that market's* prices; the joint version takes the fixed point over the pair of price vectors at once. v3: "I assume this construction goes through; it has the same shape as the paper's §5 and I see no obstruction, but it is an assumption, not a citation." **This is the largest single unproved input to the v3 route.**
- **Relativization is an obligation.** Recurring Unbiasedness (4.8.15) is proved for weightings generable from a *single* market's prices. Its proof (appendix D.2) builds the exploiting trader *from* the given weighting, used as a black box, and nothing there appears to use minimality of the feature language — so it *should* hold verbatim for the joint class against the joint criterion. v3 flags this as the one place a verifying reader should open the paper's proofs. Theorem 2 leans on it harder than Theorem 1, because its firing weighting is itself price-responsive.
- **It is a hypothesis, not bookkeeping.** v3 is explicit: under strict alternation one side's day-$n$ features see only the other's day-$(n{-}1)$ output, and a single day can move a price by $\Theta(1)$, which nothing in the argument controls.

---

## 2. What it is actually buying

Exactly one thing: it makes the **violation gate** $\mathcal C_A$-generable.

$$w_n = \operatorname{Ind}_\delta(a_n > t)\cdot\operatorname{Ind}_\delta\big(\mathbb E^H_n(X_n) < t-\varepsilon\big)$$

reads the same-day *pair*. The first factor is a ramp on $A$'s own quote and is free ([[faithful-acceleration-result]] §3). The second factor is a ramp on **$H$'s day-$n$ price**, and the A-side unbiasedness average has to be taken against $w_n$ itself — so $A$'s traders must read $H$'s day-$n$ price. Joint clearing is how v3 pays for that, and it is the *only* thing it pays for.

This is worth saying flatly because it localises the assumption. Joint clearing is not a background feature of the setting; it is the price of one factor in one gate. Change the gate and the assumption goes away — which is what the other two routes in [[faithful-acceleration-result]] §4 do.

---

## 3. One-way visibility is much cheaper, and it is the realistic direction

The correction is FA-chat msg 39, which retracts v3's own framing:

> continuity is only required in a trader's *own* prices, because those are the fixed-point variables of its market's clearing; the cross-market stream is settled data at read time, so hard dependence on it is fine — my "jointly continuous in the pair" overstated the requirement.

So the two directions are not symmetric in cost:

| arrangement | what is needed | cost |
|---|---|---|
| **mutual, same-round** | one fixed point over both price vectors | a new Brouwer argument; existence **assumed** |
| **one-way, sequential** ($A$ clears, then $H$) | $H$'s traders depend on $A$'s day-$n$ quote as *settled data* | **none structural** — hard dependence on settled data is legal; no joint fixed point |
| **neither** | nothing | none |

Under sequential clearing there is no fixed point to construct: $A$'s market clears against its own prices in the ordinary way, its quotes are then decided, and $H$'s market clears with those quotes available as constants. Standard composition.

**And one-way is the direction the application wants.** Abram's framing of the training-run picture (FA chat msg 42): the AI equilibrates against frozen human data, *then* humans equilibrate with access to the frozen AI. The human reads the AI's published forecast; the AI does not read the human's current beliefs. So the cheap direction is also the realistic one, and the expensive symmetric assumption was never what the application needed.

---

## 4. Consequences for the three routes

- **v3's route** needs $A$ to read $H$ ⟹ mutual same-round ⟹ the assumed Brouwer construction plus the D.2 relativization obligation.
- **Theorem A** ([[delay-and-visibility]] §2) needs **no visibility in either direction**: convergence collapses the human-side factor into a constant, so the gate is a function of $A$'s own quote. No joint clearing, no relativization obligation — the weighting lives in a single market's class, which is what 4.8.15 is stated for.
- **The `cee` route** ([[faithful-acceleration-result]] §4.3) needs only **one-way** visibility: it moves the human-side burden onto $H$'s *own* Recurring Unbiasedness, so $A$ never reads $H$. Its cost is elsewhere — the common-subsequence gap — not here.

So the assumption's status has changed. It is no longer "the setting in which faithful acceleration is proved"; it is one of three ways to discharge Half 2, and the most expensive of them.

---

## 5. The strict-alternation question, as it now stands

v3 §6 leaves open whether the result survives strict alternation. That question has been partly answered and partly dissolved:

- **For fixed questions: yes, and more** — Theorem A survives *arbitrary* delay, not merely one-day alternation.
- **For varying questions: reduced to a different question.** The obstruction v3 worried about (one-day staleness uncontrolled, a day can move a price by $\Theta(1)$) is real for *its* gate, but the `cee` route does not use that gate. What is open there is the common-subsequence gap, not the alternation.
- **The matching impossibility that would have justified insisting on joint clearing is REFUTED** — [[delay-and-visibility]] §3. So there is no negative result licensing the restriction.
- **The day-scale question** in its original form (one-day delay, joint clearing removed, v3's gate retained) remains OPEN at ~0.6 and was deliberately not sketched.

## 6. Status

| claim | status |
|---|---|
| Joint clearing buys exactly the $\mathcal C_A$-generability of the violation gate's human-side factor | PROVED (prose, this page) — reading of v3 (A1) |
| The joint Brouwer construction exists | **ASSUMED** in v3; not proved anywhere |
| D.2 relativizes to the joint class | CONJECTURED (~0.85), v3's own flagged obligation |
| One-way visibility needs no fixed-point construction | PROVED (prose) — msg 39's correction; elementary |
| Theorem A needs no visibility at all | PROVED modulo named hypotheses (~0.90) |
| Strict alternation, varying questions, v3's gate | OPEN (~0.6) |

## Related

- [[faithful-acceleration-result]] — the factoring and the three routes
- [[delay-and-visibility]] — the axes; why direction, not length, carries the weight
- [[setting-and-notation]] — Setting 1 vs Setting 2
- [[li-paper-erratum]] — 4.8.15's corrected form, and Definition 4.3.5 on generability
- [[open-problems]] — the common-subsequence gap; the day-scale question
