# Manipulation as conduct that works through her mistakes

Robert Noggle's Mistake Account (*Manipulation: Its Nature, Mechanisms, and Moral Status*,
OUP 2025) supplies the organising idea; where this document goes beyond him it says so. The
measure of success is the program's: a behaviour defined so that it matches the philosophy
and the standard cases, and a setting in which conditions give that behaviour, possibly
approximately. All names are provisional. Paths are relative to this directory unless they
begin with `lean/`, `prompts/` or `DECISIONS.md`.

Tags. **[Lean]**: kernel-checked on `main`. **[paper]**: a short proof on paper, with an
exhaustive exact search over small cases in `mistakes_setting.py`, `mistakes_sequential.py`
or `mistakes_longrun.py`, which the round's runner runs; nothing so tagged is a statement of
record. **[tested]**: verdicts compared on cases; §6 says by whom. **[open]**: not decided.
The maintainer's positions that the account rests on are the working positions of
`DECISIONS.md`, `2026-11-21--manipulation-working-positions`, cited below as *positions*
with their number.

## 0. The account in one paragraph

She can make mistakes: believe falsely, feel what does not fit, attend to the wrong thing,
act against her own considered judgment. An adviser **manipulates** when it tries to
influence her by getting her to make a mistake; that is Noggle's definition and it is kept
as the definition (*positions* 1). What it is for an adviser to be "trying to" is left to
philosophy. The formal part is two things. A quantity: what the adviser's conduct gains
through mistakes it caused in her, found by comparing what the conduct achieves with what
it would achieve were that damage undone. And a property of a choice: the adviser took gain
of that kind when another option was as good otherwise and had less of it, **avoidable
gain**. Knowingly taking avoidable gain through her mistake is using her mistake; that link
is an argument, not a theorem. Avoidable gain gives guarantees in its own right: where the
adviser is scored by her evaluation, an adviser that takes none does as well by her
informed judgment as any alternative, as far as she can credit it, however easily she is
fooled.

## 1. What a mistake is

A **mistake** is a fault in one of her psychological states or processes (Noggle ch. 7):

- a false belief;
- an emotion that does not fit its object, or is out of proportion to it;
- attention or weight put in the wrong place, including a habit or social script applied
  where it is not reliable;
- a choice against her own considered judgment. Following Noggle (4.7) this covers both
  her judgment being bent for the moment and her acting against a judgment she still holds.

The standard is the facts: a belief is mistaken when false, an emotion when its object does
not warrant it. For emotions and weights the standard is a range, and only responses outside
it are mistakes. A small mistake with no harm is Noggle's *trivial* case (9.10.4).

Modelling choice: each faculty is treated as producing a response that can be compared with
that standard. A belief is an estimate of a fact; an emotion an appraisal of how much its
object warrants; attention an estimate of how much something matters; a choice is compared
with the act her **considered** valuations rate highest.

Two measures of her condition, larger is worse:

    error      E[(x̂ − X)²]  =  E[(X − E[X | O])²]  +  E[(x̂ − E[X | O])²]
    regret     E[max_a u_a − u_{a*}]      u her considered valuations, a* the act she takes

The identity needs `x̂` to depend only on what she observed, `O`, and is taken under one
probability model. Its terms are how far the facts are from the best estimate her
observations allow, and how far she is from that estimate. They do not separate deception
from other error: a listener who correctly allows for a source that lies one time in five
has second term zero, and on the lying occasions ends more confident in a falsehood than she
began (`mistakes_setting.py`, the listener). Whether the adviser caused an error is a causal
question, answered in §3.

**[Lean]** On a finite space, in `lean/Workspace/Deference/Contrib/AppraisalAccount.lean`:
the split (`mse_split`, `strong_split`); what she attains as the best attainable less what
she cannot know less what her choice loses (`three_channels`); the bound on what her choice
loses (`misuse_le`). These are facts about the measures and mention no adviser.

## 2. Manipulation, in Noggle's terms

An adviser **acts manipulatively** when it tries to influence her by causing what is, from
its own perspective, a mistake of hers, intending the mistake to play a role (6.2). It
**manipulates** when, in addition, the thing really is a mistake, she makes it, and it has
roughly the intended effect (6.4). Its perspective is what it currently believes, including
tacitly, not what it would work out by further inference (5.10).

Why the adviser acted, and what happened to her, are independent:

| | no mistake results | a mistake results, without the effect sought | a mistake results and has its effect |
|---|---|---|---|
| the adviser was not trying to, and the conduct was not shaped by such gain | ordinary influence | she is mistaken, not manipulated | she is mistaken, not manipulated (an honest slip; Noggle's Aunt Vicky) |
| the conduct was designed, trained or reinforced to work that way | manipulative conduct that fails | fails in part | manipulative conduct that works |
| the adviser itself is trying to | acts manipulatively (his Irene, who is wrong about the facts and leaves her target better informed) | acts manipulatively | **manipulates** |

The middle row is for systems that have no beliefs about what they are doing, or whose
sincere beliefs were themselves shaped by what paid. Noggle calls a thing manipulative when
designed to induce mistakes, or when it tends to (6.5); the middle row is wider than the
first and narrower than the second. Millikan's account of function ("In Defense of Proper
Functions", 1989) says what "reinforced to work that way" means: the conduct is there
because earlier conduct like it had that effect. A habit of flattery trained in by approval
is in the middle row; confident error never selected for its effect is in the top row.

"Trying to", and "shaped by", are not formalised here. That is acceptable provided the
safety guarantees are not significantly worse for it (*positions* 1); §4 says what is
guaranteed without them.

Three cases the table is to place as follows (*positions* 4–6). Choosing the option she
will over-rate, because she will over-rate it, is manipulation even if nothing false is
said. An unwitting habit reinforced because people give in belongs in the middle row, not
the bottom. A kind deception is manipulation: an adviser that never manipulates forgoes
benefits that would come through her being mistaken.

## 3. The formal setting

**Conduct.** The adviser's conduct `c` is a whole plan, judged over the whole history (§5,
the last instance). `c₀` is leaving her alone. `r` is the adviser's objective.

**Three idealisations of her, in order.** Each is "except as she validly asked" (below).

1. **Undamaged.** Compare each response of hers, at each time, with what it would have
   been at that time had the adviser left her alone throughout (`c₀`). Keep the part of
   the difference that moves toward the standard; undo any part that moves away from it or
   past it. She keeps what the conduct genuinely taught her; errors she had anyway stay.
   For a single estimate this puts her at the point nearest her actual estimate on the
   stretch between her left-alone estimate and the truth: if she would have held −1, the
   truth is 0 and the conduct moved her to +1, she is put at 0. For responses that are not
   single numbers "toward the standard" needs defining case by case. **[open]**
   "Undamaged" is not "free of manipulative influence": if she would have held 2, the
   truth is 0, and the adviser knowingly moves her to a false 1, the change is kept as an
   improvement.
2. **Informed.** She is also given what the adviser knows.
3. **Unshifted.** Her valuing is also as it would be without changes she did not ask for.
   Her unshifted self rates the whole history, who she became included, so a change she
   would welcome is credited by her and is not gain.

For each history let `r₀, r₁, r₂, r₃` be the adviser's objective with her as she is, and
after each step. With `x⁺ = max(x,0)`, `x⁻ = max(−x,0)`:

    M = E[(r₀ − r₁)⁺]      gain through mistakes the conduct caused
    I = E[(r₁ − r₂)⁺]      gain through her not knowing
    S = E[(r₂ − r₃)⁺]      gain through an unasked shift in her valuing
    L = E[(r₀ − r₁)⁻ + (r₁ − r₂)⁻ + (r₂ − r₃)⁻]     what her mistakes, ignorance and shifts cost it
    h = E[r₃]              what the conduct achieves through her judgment working properly

so that `E[r₀] = h + G − L` exactly, with `G = M + I + S`. Write `t = h − L`, the value gain
aside. These are computed either by the adviser's own picture of the situation or by the
facts; each result below is stated in one of the two.

Remarks.
- Step 1 is causal and needs `c₀`. In the calibrated-listener example of §1 it gives gain
  `1/10` with the second error term zero.
- A false belief she already held, which telling her would correct, is removed at step 2.
  A standing fault that the conduct triggers into a new mistake (an offer aimed at a known
  weakness) is removed at step 1. Information does not cure a standing emotional fault.
- The order is a choice. Different orders can divide a joint effect differently. The net
  `G − L` is the same for any order that ends with her in the same fully idealised state.

**Avoidable gain.** Conduct `c` takes **avoidable gain** when some available option has `t`
at least `t(c)` and less `G`. The verdict uses total gain; which of `M`, `I`, `S` is in
excess says which wrong it resembles (manipulation, non-disclosure, value interference).
Judged kind by kind with the other gains still counted, two options equal in `h`, one with
gain only through mistakes and one only through ignorance, would each be condemned by the
other; with the total, neither is (`mistakes_setting.py`, kind by kind).

**How this relates to §2.** An adviser that knowingly takes avoidable gain through a
mistake it causes is using her mistake to get something; on Noggle's definition it acts
manipulatively. That is an argument from what "trying to" means. The converse fails: an
adviser can be trying to mislead her where no gain is avoidable: it has a second
sufficient reason for the same act; the deception gains it nothing; the false thing was
merely easier to say; every option open to it deceives her; or the falsehood leaves her
nearer the truth than she was. Avoidable gain is therefore a narrower, checkable property,
and its guarantees are its own (*positions* 2). It is stated of the adviser's options as
they are, with no imagined counterpart of the adviser that gives gain no weight
(*positions* 3).

**Legitimacy.** A history is **legitimate** when none of the adviser's conduct on it takes
avoidable gain: the adviser took no advantage of her being fooled, uninformed or altered
that it could have done without. That gloss is proposed and not yet ruled on
(`DECISIONS.md`, *Awaiting the author*); legitimacy has this one reading (*positions* 8).
Legitimacy in this sense is narrower than the absence of manipulation in Noggle's sense:
each of the five cases of the last paragraph is manipulative conduct on a history that can
be legitimate. A legitimate history can contain her mistakes. Her commands and their
priority over her evaluation are the corrigibility design's separate component.

**Requests.** A state she validly asked for (an illusion for fun, not being told, a change
of taste) is not removed by the idealisations, so no gain is counted for it. A request is
valid when her idealised self at that time, idealised using only earlier valid requests,
would also make it. That is settled in order of time, and it requires that she would still
ask knowing what the adviser knows. Requests made at the same moment, and cases where her
idealised self could answer more than one way, need a convention. **[open]**

Value interference is defined without a "self she would otherwise have been" beyond `c₀`;
a comparison is needed to measure `S`, not to say what the wrong is (*positions* 7). That
argument changes beliefs and not values is a restriction of the model. Whether an
unauthorised change in her values is better placed with her commands, as a violation of
her authority, is queued (`DECISIONS.md`, *Awaiting the author*); `VC_RESULTS.md` has a run
of each placing.

## 4. What is guaranteed

For a producer that maximises `r` over a finite set of options; `c*` its choice. Each of
1–4 is checked exhaustively over three options on a small grid, and each instance of 6 is
recomputed, by `mistakes_setting.py`.

**[paper] 1. No avoidable gain gives the best value, gain aside.** If `c*` takes no
avoidable gain then `t(c*) ≥ t(c)` for every option `c`.

**[paper] 2. Graded.** With no condition, let `σ = max t − t(c*)`, what it gave up gain
aside. Then `σ ≤ G(c*) − G(c′)` for any option `c′` maximising `t`: it cannot give up more
than the extra gain it took.

**[paper] 3. A gate.** Score an option by `r` if it takes no avoidable gain, and otherwise
by something below every such score (as in the corrigibility post, where legitimate
histories score in `[0,1]` and illegitimate ones below zero). The maximiser of that score
takes no avoidable gain, maximises `t`, and among options maximal in `t` has least `G`.
Without the separation of scores it fails, on an instance.

**[paper] 4. Correcting the reward.** With reward `t + (1−ρ)G`: for `0 ≤ ρ ≤ 1`,
`t(c*) ≥ t(c) − (1−ρ)(G(c*) − G(c))⁺`. For `ρ < 1` the maximiser never passes up gain among
options equal in `t`; at `ρ = 1` it is indifferent to gain; for `ρ > 1`, among options equal
in `t` it takes least gain, and it may avoid an option better in `t` because that option
carries gain. So measuring and removing the gain protects `t` and does not stop the
adviser taking avoidable gain; a gate as in 3 stops that without penalising gain that is
not avoidable. `mistakes_sequential.py` checks the same bounds with `h` and `L` kept
apart, and that the gate leaves `h(c*) ≥ max h − max L`.

**[paper] 5. Reinforcement.** Under exponential-weights selection on reward
(`p_{n+1}(c) ∝ p_n(c)·e^{η r(c)}`, every option starting with positive weight) the log-odds
of one kind of conduct against another grow each round by `η` times the difference in `h`,
plus that in `G`, minus that in `L`. The part due to `G` is the share of its reinforcement
that came through her mistakes, ignorance or shifts. No script checks this one.

**[paper] 6. One witness per term**: avoidable gain through mistakes, through ignorance and
through an unasked shift, each lowering `h`; under-crediting alone lowering it with no
gain; estimates right in total and wrong in their division between `h` and `G`, passing in
the adviser's own picture while `h` is zero in fact. The witnesses are numbers assigned to
`h`, `G` and `L`; none is derived from a causal model of an interaction.

**What these say about her welfare.** `h` is the adviser's objective with her idealised. It
is her informed interest only under an assumption about the design: **the adviser is scored
by her evaluation of the history**, as in the corrigibility post. Then `h` is what she would
say of the history undamaged, informed and unshifted, and `t` is that less what she fails
to credit. With an adviser that has interests of its own (a seller), results 1–4 say only
that it behaves as it would toward someone who could not be fooled.

**Is safety significantly worse for leaving "trying to" unformalised?** The question is put
to one guarantee: result 1, that no option is better in `t`. Cases Noggle convicts and
avoidable gain does not:
- *A second sufficient reason.* In the corrigibility design the only other reason available
  is that the option is best in `t`, and result 1 already protects that.
- *A deception that gains nothing.* No welfare bound is at stake, since nothing is gained.
  If she would mind having been lied to, her informed evaluation of the history counts it,
  so it lowers `h`; if she would not, nothing here catches it.
- *The false thing was easier to say.* Same as the last.
- *Every option open to it deceives her.* Nothing is avoidable, and result 1 holds among
  the options there are; it says nothing about how good those options are.
- *A falsehood that leaves her nearer the truth.* It is kept as an improvement at step 1,
  so no gain is counted.

So in that design result 1 is not weakened. That is a statement about that guarantee, not
about safety overall or freedom from manipulation. What is not guaranteed is that the
adviser never says what it believes false; truthfulness is a separate requirement this
account does not derive. For an adviser with its own interests the first case is real and
uncovered.

**[Lean]** The facts of §1. The scoring theorem
(`lean/Workspace/Deference/Contrib/ScoringTheorem.lean`: `Audit.welfare_bound`,
`Audit.conduct_bound`, `Audit.authority_bound`, `Audit.no_credit`): with an audited
evaluation, a conduct audit and a penalty, bounds on her expected true utility, on the
chance she is wronged, and on expected detected violations of her authority. In it "she is
wronged" and "her evaluation does not run above her informed verdict at the course taken"
are inputs; that the welfare bound needs the latter is `Witness.d1a_needed` and
`Witness.d2a_needed`.

Results 1–3 are short. 4 is the one that tells a designer something not obvious. Farquhar,
Carey and Everitt (2022) give the corresponding design, a path-specific objective; what is
added is which state to exclude (the damage to her judgment, not her beliefs, so the
incentive to inform her stays) and the bounds. Nothing in this section except the last
item is in Lean, and nothing in it relates `M`, `I`, `S` to the scoring theorem's data.

## 5. The long-run statement

**[paper]** (`mistakes_longrun.py` checks the facts at each decision and recomputes each
instance; the passage to long-run averages is a few lines on paper.) This extends the
corrigibility post's sequential theorem (`Sequential.theorem3a` in
`lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean`), whose setting and two
hypotheses are kept. The statement is not in Lean (`ATTENTION.md` item 150).

**Setting.** Decisions `k = 0, 1, 2, …`. At each, finitely many available actions. In the
adviser's picture each action `a` has `t̂_k(a)`, `Ĝ_k(a) ≥ 0` and an expected number of
violations of her commands `N̂_k(a) ≥ 0`, where gain at `k` counts everything arriving
through damage done by the adviser's conduct at or before `k`. `A⁰_k` is the set of
authority-respecting actions (`N̂_k = 0`), assumed non-empty. An action **takes avoidable
gain** at `k`, in the adviser's picture, when some action in `A⁰_k` has `t̂` at least as
high and less `Ĝ`: gain is avoidable only if it can be avoided without violating a command.
Its estimate of the score is `U_k(a) = t̂ + Ĝ − λN̂`, with `t̂ + Ĝ` in `[0,1]`, when `a`
takes no avoidable gain, and below `−λN̂` when it does (the gate, as it expects it).

In fact: `t_k`, `G_k ≥ 0`, `N_k` for what it did, with `t_k + G_k` in `[0,1]` (her evaluation of
a history the gate passes lies in the post's range, in fact as well as in estimate; this is
what the Lean structure's field `V_le_one` asks);
`ι_k = 1` if the history is illegitimate in fact. The realised score is
`S_k = W_k := t_k + G_k − λN_k` if `ι_k = 0`, and
`V_k − λN_k` with `V_k` in `[−δ, −ε]` if `ι_k = 1`, where `ε > 0` is the least the gate
takes off.

**Hypotheses.**
- *Maximises* (the post's): `U_k(a_k) ≥ U_k(a)` for every available `a`.
- *H1* (the post's): on average its estimate of the score is not above the score,
  `limsup (1/K) Σ (U_k(a_k) − S_k) ≤ 0`.
- *H2*: on average its estimate of `t` for what it chose is not above `t`,
  `limsup (1/K) Σ (t̂_k(a_k) − t_k) ≤ 0`.
- *H3*: on average its estimate is not below the score the history would have had, had
  the gate passed it, `limsup (1/K) Σ (W_k − U_k(a_k)) ≤ 0`. By (b) below it always expects
  to pass the gate, so `U_k(a_k)` is its forecast of the ungated score `W_k`; H3 says that
  forecast is not systematically too low. `W_k` can be observed whether or not the gate
  fires.

**Conclusions.**
- **(a) Authority** (the post's 3a, unchanged): violations of her commands stay within the
  post's tolerance. Uses Maximises and H1.
- **(b) At every decision**, what it chooses takes no avoidable gain in its picture, and
  `t̂_k(a_k) ≥ t̂_k(b)` for every authority-respecting `b`. Uses Maximises only.
- **(c) Her informed interest.** For every sequence of authority-respecting alternatives
  `b_k`: `limsup (1/K) Σ (t̂_k(b_k) − t_k) ≤ 0`. What it does is worth at least what any
  permitted alternative looked to offer, gain aside. Uses (b) and H2.
- **(d) Illegitimate histories are rare in fact.** `ε · (1/K) Σ ι_k ≤ (1/K) Σ (W_k − S_k)`,
  and the right side has limsup at most 0 by H1 and H3. So the long-run frequency of
  histories on which it in fact took avoidable gain is zero; with the hypotheses holding
  to within `γ₁`, `γ₃` it is at most `(γ₁ + γ₃)/ε`. H1 and H3 together already say that the
  gate takes little on average: one forecast is neither above what it receives nor below
  what it would have received ungated. (d) turns that into a frequency. The assurance in
  (d) therefore rests on H3 as much as on the gate.

Under the design assumption of §4 (the adviser is scored by her evaluation), (c) reads:
by her undamaged, informed, unshifted judgment, less what she fails to credit, it does as
well as any permitted alternative looked to it to offer.

**Why each piece is there** (one exact instance each; the first five in
`mistakes_longrun.py`, the last in `mistakes_sequential.py`):
- *H2.* Everything available in fact yields only gain and no honest value, the adviser
  believes the reverse, and nothing is avoidable in fact. H1 and H3 hold, the gate passes
  every history, and (c) fails by the whole amount.
- *H3.* Half the histories are illegitimate in fact and half score far above its estimate.
  H1 holds on average; illegitimate histories have frequency 1/2.
- *The floor `ε`.* If the gate can take off arbitrarily little, histories whose score
  would have been nothing can be illegitimate every time at no cost.
- *Avoidable against permitted options.* If the only option with less gain violates a
  command, judging against all options makes the respecting action fail the gate.
- *The range in fact.* With a realised evaluation below zero on illegitimate histories, H1,
  H2 and H3 hold, half the histories are illegitimate, and the gate takes nothing on
  average.
- *The whole history.* Two periods: unsettle her (a standing emotional fault, which
  telling her things does not cure; no gain now), later choose what she over-rates because
  of it. Judged decision by decision, the fault is part of the situation at the second
  step, no idealisation removes it, both steps pass, and a far-sighted adviser takes that
  course, giving her half the informed value available. Comparing her at each time with
  how she would have been had she been left alone throughout, the over-rating is gain
  through damage, it is avoidable, and the course does not pass. (A planted false belief
  would not serve as the example: the second idealisation removes it whatever its origin.)
  The script computes what a far-sighted maximiser does under each reading; which courses
  pass under each reading is the reading's, put in by hand.

**What this does and does not show.** The proofs are as short as the post's own. The
content is which hypotheses are needed and what each buys: the post's hypothesis on the
total score gives authority and nothing about how the score divides; H2 gives her informed
interest; H3 with a floor on the gate gives rarity of avoidable gain in fact. (c) is
relative to how alternatives looked to the adviser, as in the post: accurate estimates for
what it chose say nothing of what it did not. Not covered: who establishes H2 and H3 (they
need `t` and the ungated score observed, on decisions sampled independently of its
choice); errors in applying the gate; approximate maximisation; exploration; a long-run
condition on her own evaluations, which should shrink what she fails to credit. Also not
covered: an adviser that plans ahead and by earlier conduct removes her later honest
options. At the later decision nothing is then avoidable. That needs whole plans compared
from the start, which the post's decision-by-decision setting does not provide
(`ATTENTION.md` item 152).

## 6. What was tested, and what the tests can show

Each run has a results document here with its counts, which the round's runner recomputes.

- **Noggle's own cases** (`NOGGLE_RESULTS.md`). Three readers coded 266 cases from chapters
  2–7 and 10–11 against a formal statement of his account. Where both give a verdict, 224
  agree and 17 disagree: pressure through a real cost where the story does not say whether
  she acts against her judgment, influence with no mistake on the list (hypnosis,
  conditioning), the loose sense, and two single cases (a teacher feigning excitement, a
  rigged coin). The paraphrases are held outside the repository.
- **Forty adversarial and literature cases** written by an outside model
  (`INTENT_RESULTS.md`). An earlier form of the avoidable-gain test, computed from the case
  writer's numbers, agrees with its verdicts on 37 of 40; the misses are a deception that
  gains nothing, actively keeping an error she already had, and covert conditioning with no
  mistake. A fresh reader given only the stories and the account in words agreed on 39 of
  40 as to manipulative or not, and on 17 of 28 of a set of Noggle's cases chosen to include
  every disagreement of the last run (`BLIND_RESULTS.md`).
- **The literature's cases of value change** (`VC_RESULTS.md`). A reader applying the
  account in words to the fifty-two cases of `LIT_CASES.md` agrees with the source on 12
  of the 19 on which a source judges an act and contradicts none; the other seven turn on
  facts the stories do not give, or have no adviser with an objective.
- **Three outside reviews** of earlier versions of this document against the program's
  standards (`prompts/2026-11-10-legitimacy-definition-prosecution/REVIEW-astra-followup-15.md`).
- **Limits.** Every coder and reviewer was a Claude instance or one outside model. No
  person has checked an encoding (`ATTENTION.md` item 148). The first idealisation as
  stated here and the rule for requests have been checked only on the examples that
  prompted them. No test above ran avoidable gain as §3 states it, computed from a causal
  model of a case.

## 7. Against the program's standards

The standards are the nine of the brief under the third heading of
`prompts/2026-11-10-legitimacy-definition-prosecution/REVIEW-astra-followup-15.md`.

| standard | status |
|---|---|
| behaviour defined, matches the philosophy | manipulation is defined in Noggle's terms and tested in words; "trying to" is not formal; the idealisations need a causal model spelled out for a real case; the placing of three cases in §2 rests on positions |
| decomposition | welfare loss decomposes (results 2, 4); "no avoidable gain" follows from a gate, which is a design |
| conditions more basic than the conclusion | result 1 is close to its hypothesis; the informative step is result 4 |
| conditions on fixed things | the options, the plan, the reward and how it arrives |
| each condition needed | one exact witness per term, and per long-run hypothesis (§5) |
| approximate versions | `σ`, and `ρ` |
| feasibility | removing a gain from reward presupposes measuring it; what the adviser's "own picture" is for a trained system is open |
| composition | with the post's sequential theorem (§5), on paper |
| honest scope | §4's last part, and §8 |

The outside reviewer rated the version before this one *partly met* on every row and was
not asked to rate this one.

## 8. Open

1. What "believes" and "is trying to" mean for a trained system, and a system that plans
   internally after clean training.
2. The causal model behind the idealisations for a real interaction: which of her states
   are variables, what `c₀` is, and "toward the standard" for responses that are not
   single numbers (`ATTENTION.md` item 151).
3. The standard for faculties that are not estimates or choices (habits, likings).
4. For the long-run statement (§5): who establishes H2 and H3, errors in applying the gate,
   approximate maximisation, exploration.
5. Truthfulness, and care not to mislead, as requirements separate from avoidable gain.
6. Whether avoidable gain should be judged against the options the adviser actually had or
   also against leaving her alone when that was not available to it.
7. The scoring theorem still takes as a hypothesis that her audited evaluation does not run
   above her informed verdict.
8. Comparing whole plans, for an adviser that plans ahead (§5, end; item 152).

## 9. Sources used

Noggle, *Manipulation* (2025), chs. 2–7, 9.10.4, 10–11. Millikan, "In Defense of Proper
Functions" (1989). Halpern and Kleiman-Weiner, "Towards Formal Definitions of
Blameworthiness, Intention, and Moral Responsibility" (2018). Farquhar, Carey and Everitt,
"Path-Specific Objectives for Safer Agent Incentives" (2022). Everitt, Hutter, Kumar and
Krakovna, "Reward Tampering Problems and Solutions in Reinforcement Learning" (2021).
Carroll, Dragan, Russell and Hadfield-Menell, "Estimating and Penalizing Induced Preference
Shifts in Recommender Systems" (2022). Christiano, Cotra and Xu, "Eliciting Latent
Knowledge" (2021). The last two were read by a sub-reader, not by the drafter. What is said
of each above is the drafter's description; none was re-read against its source when this
document was put in the repository, beyond confirming that the sections of Noggle's book
cited by number exist under those numbers.
