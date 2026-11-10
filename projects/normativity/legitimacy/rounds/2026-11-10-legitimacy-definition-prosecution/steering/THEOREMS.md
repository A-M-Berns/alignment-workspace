# Candidate statements C1–C8

Each statement is as `DEFINITIONS.md` §3 makes it exact. One status each. Rerun
everything with `python3 run.py` from the round directory; `python3 run.py
--steering-json` prints the data every number below is read from. The runner fails if a
status here differs from what the checks compute. Checks are in `theorems.py`; the
abstract layer is `value.py`.

Every *holds* is a statement about the enumerated domain named, not a theorem beyond it,
unless a complete proof is given.

## C1 (information helps every goal)

**Status: holds** on the stated domain.

(a) `|W| = 3`, `|A| = 3`, payoffs in {0, 1}: for all 512 goals and all 5 disclosures,
`AV(g, f) ≥ AV(g, baseline)` (`value.c1a`). (b) `|W| = 4`, `|A| = 2`, payoffs in {0, 1}:
over 256 goals and all 225 ordered pairs of disclosures, `f` is at least as good as `f′`
for every goal iff `f′` is a coarsening of `f` (`value.c1b`).

Hypothesis: her belief and decision parts are working. This is Blackwell's theorem
restricted to deterministic disclosures (`PRIOR_WORK.md` §1); nothing is added but the
check. The hypothesis is used: N7's true statement leaves a reader who is not working
miscalibrated. Whether a true statement can put such a reader below the baseline was not
tested.

## C2 (a lie is not a coarsening)

**Status: holds** on the stated domain.

`|W| = 3`, `|A| = 2`, payoffs in {0, 1, 2}, 729 goals, all 279 believed lies, 5
disclosures (`value.c2`). (a) Every lie has a goal whose attainable value it puts below
the baseline. (b) No lie has the same attainable value as a disclosure for every goal.

(b) follows from (a) and C1(a): a disclosure is never below the baseline. With payoffs
in {0, 1} only, (a) was not tested. A lie can also raise attainable value above the
baseline for some goal: the lie "world 0" told in worlds 0 and 1 and "world 1" told in
world 2 gives 2/3 against 1/3 for the goal the data names.

## C3 (offers and threats)

**Status: refuted.**

Fixture layer, `G = {−1, 0, 1}^goods`; `G+` is its non-negative part.

| | L0 | `G`: goals / falls / rises | `G+`: goals / falls / rises |
|---|---|---|---|
| T2, the offer | holds | 27 / 0 / 6 | 8 / 0 / 4 |
| T1, the threat | fails | 9 / 1 / 3 | 4 / 1 / 0 |
| X-gift, a payment attached to `refuse` by a world-write | fails | 9 / 0 / 3 | 4 / 0 / 2 |

(a) holds: the offer lowers attainable value for no goal. It is the monotonicity of a
maximum over a larger menu. (b) is refuted: the threat raises attainable value for three
goals of `G`. Counterexample, `cases/x_threat_welcome.py`: at the goal weighing money 1
and the house −1 she refuses, the house burns, and her value is 10 against 0 at the
baseline. On `G+` (b) holds: the threat lowers one goal and raises none. (c) The
criterion "`ΔAV ≥ 0` for every goal" agrees with the first pass's transition-function
reading of L0 on T1 and T2 and disagrees on `cases/x_gift.py`: L0 convicts a unilateral
improvement of an option's consequence, and the criterion, on `G` and on `G+`, does not.

What survives: (a); and (b) for goals that weigh every good non-negatively.

## C4 (the driver as a guarantee)

**Status: holds** on the stated domain, under the condition stated.

Abstract layer, belief part; `|W| = 4`, `|A| = 2`, payoffs in {0, 1}, 256 goals
(`value.c4`). *Weak*: for every `g`, `AV(g, d) ≥ min over u ∈ U(g) of S(g, u)`. *Strict*:
strictly for some `g`.

| driver `d` | `U(g) = {−g}` | `U(g) = {g}` | `U(g) = G` |
|---|---|---|---|
| full disclosure | weak, strict | weak only | weak, strict |
| one-bit disclosure | weak, strict | **fails** | weak, strict |
| baseline | weak, strict | **fails** | weak, strict |

The weak part is, unrolled, "some aim in `U(g)` steers her to no more than the driver
gives". Two sufficient conditions hold on the domain. *The driver is the full
disclosure*: no condition on `U` is needed, and none could be, since `AV(g, full)` is the
pointwise maximum. *`U(g)` contains an aim opposed to `g`*: any driver. Proof, complete
for the abstract layer: the adviser with aim `−g` brings about at each world the
inducible action worst for `g`; the action a disclosure leads her to is inducible; so
`S(g, −g) ≤ AV(g, d)`.

A `U` under which it fails: `U(g) = {g}`, an adviser whose aim is hers, against a driver
that cannot carry everything. Counterexample: the goal that needs worlds 2 and 3 told
apart; the one-bit driver gives 1/4, the aligned steerer 1/2.

What survives of reverse convergence: following the driver is a guarantee against the
worst adviser in `U`, and it is the best policy outright only when the driver is the
whole truth. Where she can take in less than the adviser knows, an adviser steering by
her own aim does better for her than any fixed driver. Decision, aims and options parts
were not tested; for aims the comparison has no goal to be evaluated by once the aim
itself is what moves.

## C5 (stake invariance)

**Status: refuted** as written.

Fixture layer, 38 variants of the 33 cases. (a) Faithful-adviser acquits ⇒ the decisions
part is the same for every policy: no counterexample, and true by definition. The
converse fails on 8 variants — B5 is one: the withholding moves her beliefs and no
decision. Her decision trace being one function of the world, her aims and her seed does
not give the standard.

(c) Abstract layer, `|W| = 3`, `|A| = 2`, payoffs in {0, 1}: any two different beliefs
give different decisions for some one of the 64 goals (`value.c5c`). So the statement
holds with "for every `g ∈ G`" in place of her actual goal, for the belief part.

(b) With L1 in pairwise form and the replay form:

| implication | over the 38 variants |
|---|---|
| faithful-adviser acquits ⇒ L1 | no counterexample |
| L1 ⇒ faithful-adviser acquits | fails: B4, and 16 more |
| faithful-adviser acquits ⇒ replay form | fails: N5, N6 |
| replay form ⇒ faithful-adviser acquits | fails: B4, and 16 more |
| L1 ⇒ replay form | fails: N5, N6, T1, T5 |
| replay form ⇒ L1 | fails: T7 and N9 under the multiset individuation |

Faithful-adviser ⇒ L1 is forced: equal `Z`-traces across the class leave L1's pairwise
test nothing to find. N5 separates the replay form from the standard in one direction —
an authorized write is not in `L` — and B4 in the other.

## C6 (the ordering)

**Status: holds** on the stated domain.

Faithful-adviser acquits ⇒ arm's-length acquits, by definition: an arm's-length
conviction needs a part that differs. Not conversely: N8, and N11, B4, B6, T2, T6, T8.

All twelve implications over the 38 variants; a cell names separating variants.

| ⇒ | L0–L3 ∧ W | replay form | arm's-length | faithful-adviser |
|---|---|---|---|---|
| **L0–L3 ∧ W** | | N5, N6 | N1, N3, N7, N9/sequence, T7/sequence | those, and N8, N11, B4, B6, T2, T6, T8 |
| **replay form** | N14, B5, T3, N9/multiset, T7/multiset | | N1, N3, N7, N14, B5, T3, N9, T7 | those, and N8, N11, B4, B6, T2, T6, T8 |
| **arm's-length** | none in the bank; X-fault | N5, N6 | | N8, N11, B4, B6, T2, T6, T8 |
| **faithful-adviser** | none in the bank; X-fault | N5, N6 | none (by definition) | |

On the bank, acquittals nest: faithful-adviser ⊂ arm's-length ⊂ L0–L3 ∧ W. The second
inclusion is a fact about these 38 variants and not a theorem: `cases/x_common_fault.py`,
outside the bank, has every policy make the same unlicensed write to her values, which
L3 convicts and both standards return as `broken, not steered`. The replay form is
comparable with none of the three.

## C7 (steered is not harmed)

**Status: holds** on the stated domain.

New cases, her seed aim, `ΔAV` of `own` against the adviser absent, faithful-adviser
verdicts.

| | value rises | value falls |
|---|---|---|
| steered | N3 (+1/2), N4, N7, N8, N9, N11, N14 | N1 (−1/2) |
| not steered | N5, N10, N12, N13 | N2 (−1/4) |

Broken, not steered: N2, N6. Steered with every part working: N8, N11. "Steered" and "her
attainable value falls" are independent in both directions on these cases. The value
rises in N3 because B pays more and her rule, which ignores payoffs, defaults to A.

## C8 (what the account says of the adviser itself)

**Status: open.**

The condition (`DEFINITIONS.md` §1.6): everything the adviser does is the same for every
policy of `V` at each world. As defined it holds on no variant, because every class
contains a twin that differs in a write `Z` does not read. Setting those writes aside — a
form introduced after the freeze and reported as a diagnostic — it holds on ten variants
and agrees with the faithful-adviser verdict on her side on every variant except one:
**T12**. There her protected state is the same under every policy and the adviser's
outputs are not: the complier gives the same answers without grounds.

So the condition does separate T12 from every other case, and for a reason it cannot
state: it registers that the outputs differ, not that what differs is the giving of
reasons. An adviser who added a gratuitous true remark she did not take up would fail it
the same way. T12 stays outside the account.
