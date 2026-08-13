# Repair language

What the theorem needs from the class of repairs, and what it can legitimately
leave as a hypothesis.

## The minimal typed shape

A certified surgical repair is five pieces of data:

```
selector      a public predicate of the state
source        one response
replacement   a response, possibly state-dependent
certificate   the public normative reason licensing the rewrite
scope         the subject matter or standing the certificate is relative to
```

with the induced map the identity off the source. Five constraints:

| constraint | why |
|---|---|
| **causal** | the selector reads the state as the date opens, never the current sample |
| **loss-blind certification** | otherwise lawfulness is "it helps", and the normative reading is gone |
| **fixed as a program** | the record holds strings; no callable, no closure, no horizon |
| **surgical** | a rule rewriting several actions lets gains and losses cancel, and the lower bound dies |
| **complexity-controlled** | `K` enters the regret bound as `log K`, so a class may be large but must be finite or otherwise controlled |

`log K` is generous: the class can grow substantially before the bound degrades,
which is what makes a generated grammar plausible rather than hopeless.

## Two questions that must not be run together

**Regret against represented repairs.** A theorem. Instantiated here.

**Coverage of the repair language.** Whether the class contains a repair for each
failure class a practice needs. An expressivity question, entirely open, and
legitimately a hypothesis:

```
for every failure class P in the target family, some g in Gcal repairs it
```

The theorem does not have to solve normative adequacy internally. It has to state
that it is not solving it.

## The recurrence constraint, which is new

A second adequacy condition, not previously articulated, from
`LEARNING_DYNAMICS.md`:

> If every rule in the class points away from a mistake and nothing points back,
> the targeted responses are transient in the rule-mixture chain and the
> stationary construction gives them zero mass at every date the repair fires.

This does not damage the theorem — the conclusion holds in its strongest form.
It means a generated grammar cannot be validated by checking coverage alone: a
class can be adequate in the expressivity sense and still make its own conclusions
vacuous in the dynamics sense. A naive "collect every repair" construction has
exactly this shape.

## Conflict is a compiler question, not a theorem question

Two lawful repairs may share a source and send it to different replacements. The
fixture has this: `hold` is the source of both `answer_the_exposed_burden` and
`vindicate_rather_than_hold`.

Nothing breaks. The lemma is stated per repair and reads only that repair's map,
so each inequality holds independently, checked on a run where several are
simultaneously selected. What conflict affects is which repair a *compiler* should
prefer, and the theorem does not need an answer — it quantifies over the class.

Interaction the theorem does *not* control: one repair's effect on the actual
trajectory can remove occasions relevant to another, since the process is
endogenous. That changes `M_T` for the second repair, which the conditional rate
already accounts for by dividing by it.

## What a paper-level class would need

1. a generative grammar over the five typed pieces;
2. a complexity model — cardinality, description length, or a prior — entering the
   bound in place of `log K`;
3. a stated adequacy hypothesis relating the class to a target family of failures;
4. the recurrence check above;
5. a compiler soundness statement connecting a certificate's presence to the
   repair being normatively appropriate — currently absent, and the reason
   "lawful" names a discipline rather than a proved property.
