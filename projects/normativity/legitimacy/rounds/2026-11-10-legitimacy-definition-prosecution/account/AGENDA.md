# From the mistake account to legitimate influence: what would have to be proved

Against `PROMPT-followup-13.md` §4.3. The question: what separates an adviser that helps
her form and revise her judgments from one that engineers them to obtain her permission or
a favourable evaluation. The starting point is Noggle's account of manipulation as
influence that works by inducing a mistake (R. Noggle, *Manipulation: Its Nature,
Mechanisms, and Moral Status*, Oxford University Press, 2025; "The Mistake Account of
Manipulation", *Journal of Practical Ethics* 14(1), 2026, doi 10.3998/jpe.9951). Nothing
here is proved. All names are provisional.

## 1. Candidate definitions, in the workspace's terms

The objects are `ThinLegitimacy`'s: her prior, the actual process `A` to her later record,
her credence `V`, a function `g` of the world she is asked to evaluate; and §1's: courses,
what the adviser knows `k`, its score.

- **Mistake.** At a record `r`, her credence is not the actual posterior (`Correct` fails
  at `r`), or her evaluation is not `E[g | r]`, or she takes a move her own valuations
  rank below another (`AppraisalAccount.regret`). Emotions and attention are appraisals,
  and a mistake of either is a mistake of evaluation.
- **Manipulation, as success.** The course taken leaves her mistaken at a record where an
  available course does not, and her act or evaluation differs from what it would be
  unmistaken.
- **Attempt.** By the adviser's own beliefs, the course taken raises the chance or the
  size of a mistake of hers over an available course, and the adviser's expected score, by
  those beliefs, is higher through it. It needs the adviser's beliefs as an object apart
  from the truth; `k` in §1 is what it believes, and an honest error is a false `k`
  reported as believed.
- **Exploitation.** She is no more mistaken under the course taken than she was before
  it, and the course taken is not a best reply to her unmistaken response: the adviser
  built on a mistake it found.
- **Lean.** `E[v − fe | π, k] > 0` at the values of `k` at which the adviser acts: its
  errors, and hers that it leaves, favour it. This is D1(a) failing at the course taken.
- **Responsibility**, two forms.
  *Gain*: the adviser gains from her mistake and either left her more mistaken than it
  need have, or chose differently because of it.
  *Declared reference*: its channel departs from the declared reference
  (`TransparentChannel.Realizes` fails).

## 2. What each form of responsibility gets wrong

On the outside reviewer's twenty cases (`RESP_RESULTS.md`) the gain form is wrong on 8 and
the declared-reference form on 14.

**Gain.** It makes the adviser's reward a condition of its responsibility. An adviser that
induces a mistake for her good, at its own cost, for no reason, or to a script is cleared
(X1–X5), against the position that a good outcome does not excuse. An adviser that knew
nothing of a mistake of hers is convicted when the mistake pays and another course would
have corrected it (Y1–Y3): the first branch imposes a duty to correct every profitable
mistake, known or not. The second branch needs the adviser's choice under her unmistaken
response, which is a counterfactual about its reasons and is not in a table of scores.

**Declared reference.** It measures conformity to a rule and not her condition. A rule
that prescribes the manipulation clears it (X5–X10; `TransparentChannel.Witness.picker`
is the same fact: the cherry-picker realises the reference that declares its selection).
A departure that corrects, or that she asked for, is convicted (Y4–Y6, Y10). It does not
tell a mistake induced from an attempt that fails, from value interference, or from
non-disclosure (Y7–Y9). Where no reference is declared it says nothing.

Neither form uses what the adviser believed. The cases that separate exploiting a known
mistake (X8) from profiting by an unknown one (Y1, Y3) differ in nothing else.

## 3. What would have to be proved

1. **A condition on courses that helping satisfies and engineering does not.** A property
   `P` such that (i) disclosure, honest argument and correction have `P`, including
   argument that changes her mind; (ii) every course whose score is higher through a
   mistake of hers lacks `P` or earns nothing by it; (iii) `P` is a function of the record
   and what the adviser believed, so that an audit can have `κ > 0` for it. The lean
   condition is a candidate for (ii) and fails (i) on I4 of `DERIVATION.md`: selection
   among honest two-sided estimates leans by `1/8` with no dishonest step. Whether that
   adviser manipulates is the open question on careless inducing, and I4 is what it turns
   on.
2. **Attempt from success.** A statement in which the adviser's beliefs and the truth are
   separate arguments, proving that an adviser with an honest error has no expected gain,
   by its own beliefs, from her resulting mistake; and that D6 with the adviser's
   expectations in place of correct ones bounds what the honest error costs.
3. **Inducing from her condition.** A measure of the mistake attributable to the course:
   her miscalibration under the course taken less under a reference course. It needs the
   reference course fixed without circularity; the candidates are the honest course of D5
   and the adviser's absence, and the eleventh follow-up found the second undefined where
   an adviser cannot do nothing.
4. **The process conditions for an evaluation.** `DERIVATION.md` gives D1 from the process
   conditions for an evaluation that is her credence's expectation of a fixed function. To
   prove: the same where what she evaluates is her own later verdict, and where her model
   of the adviser's errors is learned from past audits and not assumed.
5. **D2 from a condition on her valuing over time.** A statement that her valuing at the
   evaluation is a function of the admitted reasons and her earlier valuing, with a
   witness that separates a reason about what is the case from an input that moves what
   she wants.

## 4. Legitimacy for authorisation and for feedback

Her judgment is **legitimate** when the adviser did nothing to corrupt it. This is what
her permission needs, and it is a condition on conduct alone: authorship, a channel that
is what it is declared to be, disclosure, no change to her valuing she did not ask for. A
legitimate judgment can be mistaken (I2: an honest slip leaves her wrong and her permission
stands). The existing statement of this kind is `Legitimacy.Segment.payload_of_view`:
under authorship and transparency her verdict is a function of the declared inputs. To
prove: that a permission so produced is hers in the sense the authority module consults,
with the violation count `N` defined from the module's events; `BRIDGE_LEAN.md` §4.2 names
the missing map.

Her judgment is **sound** when it is legitimate and she reasoned correctly. This is what
using her evaluation as a measure of her welfare needs, and it is D1: the conduct
conditions together with her coherence and a correct model of the adviser. To prove: item
4 above. The two are independent in one direction only: sound implies legitimate.

## 5. What strict priority of authority requires

§1's (3) is `E[N] ≤ α(1 − u* + Δ)/lam`: for any finite `lam` a course with a small chance
of a detected violation is taken when its evaluation is high enough. Strict priority says
no gain in evaluation is traded for a violation. It requires one of:

- **a constraint in place of a penalty**: the adviser chooses among the courses with
  `N = 0`, which exist by D5, and (1) is then a bound against the best such course with no
  `lam` in it;
- **a lexicographic score**, with the count compared first.

Either needs what a penalty does not: that every violation is detected, since `N` is the
detected count and an undetected violation is invisible to both; and that the adviser can
tell before acting which courses have `N = 0`, where §1 needs only correct expectations.
The post's condition `lam > 1 + δ` (`DeconfusingCorrigibility.Scoring.theorem1`) orders
realised histories, a violated one below every violation-free one, and is not strict
priority over courses: its Theorem 2 leaves a tolerated rate `τ`.
