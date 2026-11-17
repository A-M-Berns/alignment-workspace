# The statement — three ratings, three lines

The statement of `PROMPT-followup-11.md` §1. Six of its choices, marked *(temporary)*, were
adopted by the maintainer on 2026-11-17 for the purpose of testing, on the prompt author's
recommendation; they are not rulings. The rest of §1–§8 is the prompt author's
consolidation. §9 is the executor's: what had to be added so that a verdict is computed
from a written-out case, each addition with its alternative. All names are provisional.

## 1. The bare setting

She has **options**. Each option, in each state of the world, leads to a **fully described
future**: what happens, and what it does to her. Of an option she has three ratings, each
her own, each under a different state of information:

- `r` — her rating **as things stand**;
- `R^s` — her rating once told the true chances that everything she has observed, `s`,
  supports;
- `R` — her rating once told what the future contains. Of an adviser's policy, `R` is her
  rating once told the policy's true chances.

Her **way of valuing**, `f`, is her informed rating `R`. A **mistake** is a gap between
`r` and `R^s`. A **change of values** is a change in `R` over time. A **discovery** is
told from a change of values by one test: tell her beforehand, and see whether she rates
the thing as she later will.

Assumed: under each state of information her ratings rank the options; telling her
chances or outcomes changes her information and not her valuing.

## 2. The yardstick

Fix a best and a worst fully described future. The rating of an option is the chance `q`
at which a known `q`-chance of the best, else the worst, is exactly as good to her. Every
size below, and the tolerance `δ`, is on this scale, between 0 and 1. It needs her ratings
to move continuously in `q`.

## 3. The `E[·]` setting

Assume in addition that her informed self rates a known gamble at the chance-weighted
average of its parts. Then, with `X` the facts, `x̂` her estimates of them, `U_a` the
informed rating of the future option `a` leads to and `û_a` her rating of `a` as things
stand: `r` is `û`; `R^s` is `E[U | s]`; and `R` of a policy `π` is `E[U_π]`, where
`U_π = f_now(X; π)` is her informed rating, at the moment the adviser acts, of the future
`π` leads to.

## 4. The three lines

Each is zero when nothing is wrong; larger is worse.

1. **Trickery** *(temporary)*: `E[(x̂ − E[X | s])²]` for each fact and for each of her
   utilities (`û_a` against `E[U_a | s]`). Bare form: the gap between `r` and `R^s`.
2. **Pressure**: `E[max_a û_a − û_{a*}]`, `a*` the option she takes. Bare form: the same
   in `r`.
3. **Illegitimate value change** *(temporary)*:
   `max over π that change her no more than π* of E[U_π] − max over π ≈ π* of E[U_π]`.
   Bare form: her informed ratings of those two best policies.

## 5. What line 3 is given, and what it derives

**Given.** `Π`, the policies the adviser could follow from this moment on. A policy is a
rule from what has happened so far to what the adviser does next; `π*` is the rule it
actually follows, not its next step. `ν`, the baseline for her valuing *(temporary)*: the
adviser does nothing to her valuing from this moment on, except what she asks. `δ`, a
tolerance between 0 and 1.

**Derived.** Her later valuing under `π` is `R_t^π(x)`: her informed rating of each fully
described future `x` at each later time `t`, on the yardstick. The whole path counts.

- `d(π, π') = max over t, x of |R_t^π(x) − R_t^{π'}(x)|`, in each state of the world.
- `π ≈ π'` when `d(π, π') ≤ δ` in every state.
- `π` **changes her no more than** `π*` when, in every state and for every `t` and `x`,
  `R_t^π(x)` lies between `R_t^ν(x)` and `R_t^{π*}(x)`, within `δ`:
  `min(R_t^ν, R_t^{π*}) − δ ≤ R_t^π ≤ max(R_t^ν, R_t^{π*}) + δ`.

Both classes hold `π*`, and the second lies inside the first, so line 3 is never negative.
It is zero exactly when, among the policies that change her no more than `π*` does, one
that makes the whole of `π*`'s change is rated highest.

## 6. Readings of line 3

Both sides are scored by the `f` she has when the adviser acts, never by her later `f` or
her later approval. It is applied at every moment, and a history is flagged if any moment
is. "Informed" means knowing what each of the futures compared contains, what it will do
to her included. Where she has no view about a way of being changed, that is not
permission. Where she has a view about part of a future, only that part is judged.
*(temporary)* Honest persuasion against something she wants to keep is decided by her own
attitude to being argued with about that particular thing, and by whether she can simply
decline to hear it.

## 7. Inducing, and what lies outside

Lines 1 and 2 measure her state, whoever caused it. *(temporary)* The adviser **induced**
a mistake when it would have acted differently had her mistake gained it nothing. Whether
carelessly causing a mistake counts is open.

Coercion (lowering what her options are worth) and deprivation (lowering what she can
know) are other wrongs, not manipulation. So are what is owed to third parties, a failure
to warn, upbringing, and what an adviser owes her in help.

## 8. Scoring and gate, for corrigibility

The adviser is scored by an evaluator it does not shape: her later self as she would be
under `ν`, rating what actually happens. *(temporary)* Her evaluation is void whenever
line 1 or line 2 is above tolerance, whoever caused it, and whenever line 3 is positive on
the history. She may check in and reset; the adviser's objective never counts what a
reset would bring.

## 9. What a computation needs beyond §1–§8

Each with the reading taken (**R**) and its alternative (**A**). A specification of a
case (`SPEC_FORMAT.md`) supplies the objects; `spec_run.py` computes from them and from
nothing else.

1. **The moment.** **R**: a specification describes one moment at which the adviser acts:
   the states of the world and their chances; her options; the future each option leads
   to in each state under each policy; her informed rating `R_now(x)` of each such
   future; what she has observed under each policy; her ratings `r` and estimates `x̂`;
   the option she takes; her later valuing under each policy. A history of several
   moments is several specifications.
2. **`R^s` and `E[U | s]`.** **R**: what she has observed under a policy is a label for
   each state; `E[· | s]` is the average over the states carrying her label, by their
   chances. **A**: her observations support chances other than the true ones conditioned
   on her label (she has been misled about the chances themselves); the case then needs
   more states.
3. **Line 1's size.** **R**: computed under `π*`; one number per fact and per option, the
   largest reported. **A**: their sum.
4. **The tolerance on lines 1 and 2.** **R**: the one `δ`. Line 1 is a squared size and is
   above tolerance when it exceeds `δ²`; line 2 when it exceeds `δ`. **A**: any positive
   value counts at every `δ`.
5. **The inducing test.** The adviser's objective is `G(π) = E[g(π, state, a)]`, a number
   for each policy, state, and option she takes. Her **unmistaken response** under a
   policy is to rate each option at `R^s` and take a top-rated one (the one she in fact
   took, if it is among them; otherwise each top-rated one with equal chance). "Her
   mistake gained it nothing" replaces, in the objective of every policy, the option she
   takes by her unmistaken response; write `G°(π)`. **R**: the adviser induced when (i)
   line 1 or line 2 is above tolerance under `π*`; (ii) `G(π*) > G°(π*)`, her mistake
   gains it something; and (iii) `G°(π*) ≤ G°(π)` for some other policy `π`, so that
   without the gain it had no reason to prefer what it did. **A**: (iii) strict, the
   adviser being taken to stay with `π*` when indifferent; or the replacement made in
   `π*`'s term alone. The objective reaches her mistake only through the option she
   takes; an adviser that wants her mistaken for its own sake is written with a gain on
   the option the mistake leads to.
6. **Coercion and deprivation**, measured against `π_0`, the adviser doing nothing toward
   her at all (which may or may not be `ν`). **R**: `π*` **lowers what her options are
   worth** when `E[max_a U_a]` over the options open to her is lower under `π*` than
   under `π_0`; it **lowers what she can know** when two states she can tell apart under
   `π_0` carry one label under `π*`. **A**: against `ν`; or with a tolerance. The other
   outside matters (third parties, a failure to warn, upbringing, help owed) are not
   computed: a specification names them in words where the case turns on one.
7. **The verdict on the act.** **R**: *manipulation* when the adviser induced;
   *illegitimate value change* when line 3 is positive; both where both; *another wrong
   outside the statement* when neither and `π*` lowers what her options are worth or
   what she can know; otherwise *none*. A mistake above tolerance that the adviser did
   not induce is reported beside the verdict and does not change it. **A**: a mistake
   larger under `π*` than under `π_0` counts whether or not the test finds inducing (the
   open question of §7).
8. **No view.** **R**: `R_now(x)` may be absent. A policy leading to such a future has no
   informed rating and is left out of both maxima. If `π*` is such a policy and
   `d(π*, ν) > δ` in some state, the act is an illegitimate value change: no view is not
   permission. **A**: no view is indifference, and the future is rated as `ν`'s.
9. **The bare setting, computed.** The cases describe no attitude to risk, so the bare
   setting is run on a stipulated person who rates a known gamble below its average:
   she weights a chance `p` as `w(p) = p/2` for `p ≤ 1/2` and `(3p − 1)/2` above, and
   rates a gamble with parts `q_1 ≤ … ≤ q_n` at the `q` with
   `w(q) = Σ_i [w(P(part ≥ q_i)) − w(P(part > q_i))]·w(q_i)`. A sure future keeps its
   number and the yardstick gamble at chance `q` is rated `q`, so the yardstick is hers.
   `R^s` and `R` of a policy are her ratings of the gambles; line 1 is
   `E[(r − R^s)²]`, line 2 is as in §4, line 3 is the difference of her two ratings. The
   expectations over states in lines 1 and 2 are the analyst's. Where a specification
   writes `r` as "what her observations support", `r` follows `R^s` in each setting.
   **A**: the bare setting left uncomputed, there being no attitude to risk in any case.
10. **The reference tolerance.** A case's verdict, where one is quoted without a
    tolerance, is the verdict at `δ = 1/10` in the `E[·]` setting; the others are
    reported beside it.
