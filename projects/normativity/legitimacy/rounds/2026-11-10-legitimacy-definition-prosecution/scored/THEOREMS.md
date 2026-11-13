# Statements 1–9

Each statement is about the formalization of `ACCOUNT.md`: one scene of three parts with
small sets of views, three stipulated principals, two tabulated description languages, a
fixed decomposition. A status is a fact about that formalization, computed by the check
named and compared with this file by the runner. *Refuted* means the statement as written
fails there, with the counterexample in the check; it does not mean no faithful version
holds. Rerun everything with `python3 run.py` in the round directory; one check with
`python3 -c "import sys; sys.path.insert(0, '.'); from scored import theorems as T; print(T.check_1())"`.

Numbers are at the fixed parameters (`ACCOUNT.md` §4, language A) unless said. *Serves* and
*view-best* are the two readings of what a purpose predicts (§4); the account's is *serves*.
A candidate is written `goal; belief, judge, act; say; n exceptions`.

| | statement | status |
|---|---|---|
| 1 | the weight concentrates on candidates that agree | **refuted** |
| 2 | facts or what it was handed, by principal | **refuted** |
| 3 | lying | **refuted** |
| 4 | the comparison by aim, on the bank | **holds on the stated domain** |
| 5 | the gate | **refuted** |
| 6 | intersubjectivity | **refuted** |
| 7 | stated and pursued aims | **holds on the stated domain** |
| 8 | readings 3 and 4 | **holds on the stated domain** |
| 9 | what `Legit` then is | **holds on the stated domain** |

## 1. Does the weight concentrate — refuted

**Statement.** Under each of the three principals the heavy candidates agree on each
part's purpose and on which adviser inputs harm, subvert or force which part.

**What holds.** The weight concentrates in mass. Of 4,000 distinct terms:

| principal | top 1, 3, 10 | heavy | tied at the top |
|---|---|---|---|
| corrector | 0.120, 0.361, 0.842 | 40 | 6 |
| non-corrector | 0.205, 0.615, 0.897 | 22 | 4 |
| divided | 0.140, 0.420, 0.980 | 12 | 6 |

**What fails.** The heavy candidates disagree, and most of what they agree on is that a
part has no purpose.

| principal | belief | judge | act | goal | heavy split on |
|---|---|---|---|---|---|
| corrector | `const` 0.351, `mech` 0.351, `acc_theta` 0.281, `handed` 0.018 | `const` 0.486, `mech` 0.486, `world` 0.027 | `local` 0.999 | `true` 0.911, `does` 0.082 | whether a lie is illegitimate; the kinds of `tempt` |
| non-corrector | `handed` 0.9999 | `const` 0.478, `mech` 0.478, `world` 0.039 | `const` 0.479, `mech` 0.479, `world` 0.039 | `true` 0.873, `does` 0.120 | `trick`, `tempt`, `threat`, `hard_truth` |
| divided | as the corrector | `const` 0.500, `mech` 0.500 | `world` 0.998 | `ease` 0.998 | whether a lie is illegitimate |

Read by the second predictor `mech` is `const`: a private term predicts nothing and costs
one atom, as does "for nothing". So under each principal the judging part has no purpose
at 0.95 or more of the weight, and its behaviour is carried by exceptions: its four views
on the history cost 36 bits as a table. The heaviest candidates are tables with a purpose
left at one part. **The reason is arithmetic the account fixed:** a purpose that predicts
wrongly costs 8 bits a move, a part with no purpose costs 1 or 2 bits a move off the
history, and a table of the history's views costs 9 bits a view. A purpose earns weight
only where it predicts more than seven moves in eight off the history, and under *serves*
a purpose scored by the facts mispredicts every move she makes on a falsehood.

**The cheats**, in bits above the heaviest candidate (corrector, non-corrector, divided),
with the virtue that charges them:

| cheat | bits above | charged by |
|---|---|---|
| every purpose its mechanism, as a rule | 454, 550, 452 | intersubjectivity: 644 bits, all of it. Read first-person it predicts every move; removed, it is the heaviest candidate at 0.84, 0.79, 0.84 |
| every purpose its mechanism, as a table | 14, 110, 12 | parsimony (18, 50, −8) and handles (−4, 60, 20). **Not removed**: under the corrector and the divided principal it is within 14 bits of candidates that are themselves tables at two parts |
| the opposite goal pursued badly | 326, 398, 308 | handles (284, 324, 292), then parsimony |
| the goal "whatever she does", every purpose `mech` | 458, 554, 456 | intersubjectivity, 644 bits |
| the goal "whatever she does", parts for it | 54, 230, 52 | handles (64, 208, 88); intersubjectivity 36 |
| the stated candidate altered at belief, judge, act | 120, 120, 88; 192, 288, 248; 102, 102, 86 | handles |
| the stated candidate itself | 158, 310, 140 | handles (172, 292, 180) |

**Ablations.** *No handles*: the three principals have one history, so one heaviest
candidate, `true; handed, local, local; avow; 2 exceptions`, at 0.44, with six heavy;
handles are what tells the principals apart, and with them the weight moves off purposes
and onto tables. *No intersubjectivity*: `true; mech, mech, mech; avow`, as above. *No
parsimony*: 96, 32 and 6 heavy; the same purposes. *No fit*: little change (48, 39, 13
heavy), since every heavy candidate fits the history exactly.

**Sensitivity.** *Language B*: under the corrector and the non-corrector the heaviest goal
is `does` with *say* `please`, the private goal being one atom and the creditable answer
free; purposes as in A except that the corrector's heavy candidates no longer agree on
the acting part (`local`, `const`, `mech`). The goal is not fixed across languages; the divided principal's is (`ease`).
*History* 160, 320, 640: the same heaviest candidates. *Probes counted* 2 and 4: the
same, except that at 4 the corrector's acting part also goes to `const`. *The four changes
alone*: belief `acc` for the corrector and the divided principal, `handed` for the
non-corrector, at the top; 14, 26 and 27 heavy, still split. *A missed move at 4 bits*:
`true; handed, local, local; avow; 2 exceptions` for the corrector and the non-corrector;
*at 16*: tables.

**Under view-best.** The belief part's purpose is fixed: `acc` at 0.9999 under the
corrector and the divided principal, `handed` at 0.9999 under the non-corrector. The judge
stays without a purpose (0.96, 0.99, 0.97 on `const` or `mech`). The acting part: `local`
0.52 against `world` 0.48 under the corrector; `world` under the other two, with goal
`ease` at 0.87 under the non-corrector and 0.9999 under the divided. Heavy: 13, 16, 3.
The heavy candidates still split: on `trick`, `tempt`, `threat` and `hard_truth` under the
corrector, on those and `lie` under the non-corrector, on `tempt` under the divided.

**A model of five parts with crossed purposes** was not reached.

**Check** `check_1`.

## 2. Facts or what it was handed — refuted

**Statement.** For each part, the candidates that score it by the facts outweigh those
that score it by what it was handed under the corrector, and the order reverses under the
non-corrector.

**It holds for the belief part**, under both readings: by the facts 0.281 against handed
0.018 under the corrector (*serves*; 0.9999 against 0 under *view-best*), and handed
0.9999 against 0 under the non-corrector.

**Counterexamples: the other two parts.** The judge: by the facts 0.027 against 0 under
the corrector, and by the facts again, 0.039 against 0.002, under the non-corrector; the
rest of the weight is on no purpose. The acting part: handed 0.999 under the corrector,
where the statement wants the facts; and under the non-corrector the facts 0.039 against
handed 0.0001, with the rest on no purpose. Under *view-best* the same two parts fail.

**Why the belief part comes out, and how far it depends on the probes.** Bits of missed
moves by the belief part with no exception listed, by probe family:

| | history | lie | false reason | other inputs | inst | disc | unrel |
|---|---|---|---|---|---|---|---|
| corrector, `acc`, serves | 16 | 48 | 48 | 64 | 0 | 0 | 32 (and 32 on `blk`, `opt`) |
| corrector, `handed` | 0 | 0 | 0 | 0 | 16 | 48 | 48 |
| corrector, `acc`, view-best | 0 | 0 | 48 | 0 | 0 | 0 | 0 |
| non-corrector, `acc`, serves | 16 | 48 | 48 | 64 | 16 | 48 | 48 (and 32) |
| non-corrector, `handed` | 0 | 0 | 0 | 0 | 0 | 0 | 0 |

Under *serves* the corrector's belief part is mispredicted by `acc` more than by `handed`
(she believes a lie until it is disclosed); the facts-scored purpose that carries weight
is `acc_theta` with ten exceptions, most of a table. The result at the belief part is a
count of probe families.
Under *view-best* `acc` predicts the corrector exactly except on the false reason.

**Check** `check_2`.

## 3. Lying — refuted

**Statement.** Under every principal a lie about something she will act on, told where she
would otherwise be right, is illegitimate with weight at least 99/100.

The weight of illegitimacy (the other aim silent; for the matter nothing reads, the other
aim tells the same truth without the false reason):

| | corrector | non-corrector | divided |
|---|---|---|---|
| a lie she will act on, where she would otherwise be right, *serves* | 0.281 | 0.000 | 0.998 |
| the same, *view-best* | 0.9999 | 0.868 | 0.9999 |
| a lie about a matter nothing reads, *serves* | 0.000 | 0.000 | 0.000 |
| the same, *view-best* | 0.9999 | 0.000 | 0.9999 |
| a lie to someone already wrong, both readings | 0.000 | 0.000 | 0.000 |

Under the stated candidate the first two are illegitimate and the third is not.

**Counterexample.** The non-corrector: the heavy candidates give her belief part the
purpose of taking what it is handed, a lie leaves that part serving, and her judging and
acting parts have no purpose to fall short of. The lie is illegitimate under none of them.
For the divided principal the figure is high for a reason unrelated to belief: her acting
part is scored by the goal `ease`, and the lie leaves her action worse by it.

A lie to someone already wrong is illegitimate under no candidate of the class, as the
third follow-up found for subversion.

**Check** `check_3`.

## 4. The comparison by aim — holds on the stated domain

**Statement.** Under reading 1 and the stated candidates, at least as many of the
eighty-nine cases match their evident character as under the third follow-up's comparison
(66).

**The standard**, the third follow-up's: the executor's reading of each case's evident
character, applied to its own renderings, so no independent validation. Here it is written
down per case (`theorems.EVIDENT`): *I*, an influence that should come out illegitimate;
*L*, one that should not; three left open (N8, N11, X1); D23, reported; Y1 and Y3, about
weights, matched by their banked predictions. A case matches when its computed
`illegitimate` agrees. The third follow-up's standard compared kinds; for the 66 it
counted as matching, the two agree (none of them fails now).

**Count: 77 of 89 match, 9 do not, 3 are open.** Of 93 banked rows 89 match their
predictions (`DIVERGENCES.md`).

| the third follow-up's | case | now |
|---|---|---|
| over-counts (6) | P7, Y6, X7, D14, Y9 | not illegitimate: the action is the same at every aim (P7b, P7c: aim-driven, help only). **Match** |
| | D13 a surprise party | aim-driven subversion of belief; illegitimate, there being no standing verdict in the scenario. Still convicted |
| misses (9) | X3 | illegitimate against the other side's advocate. **Match** |
| | Y1 | the alarm part is for the goal at 0.988 of the weight under the corrector, and for fleeing at a rustle at 0.9999 under the non-corrector; no threshold. **Match** (the banked prediction is for the corrector) |
| | N14, T7, N9 | aim-driven, nothing harmed, subverted or forced. Still missed |
| | Y4 | nothing. Still missed; left open by the dispatch |
| | P10 | the model has no variable for a reserved matter. Still missed |
| | Y5 | `help(judge), help(act)`, belief's gap unchanged: not illegitimate. Still missed |
| | Y3 | the idle part has the purpose `handed` at 0.9999. Still missed |
| mislabelled (1) | Y7 | harm, and illegitimate exactly when aim-driven. **Match** |
| left open (7) | D9, P13, T1 | aim-driven harm; illegitimate. **Match** |
| | D15 | aim-driven, nothing. A miss, as the dispatch flags |
| | N8, N11, X1 | reported below. Open |

**N8, N11, X1.** N8, a known advocate, against truthful reports: illegitimate with her
mechanism discounting his silence (widest 1/2) and with it not (widest 1). N11, a seller,
with the information structure restored: illegitimate under both mechanisms. X1, a known
sender, against a sender who recommends exactly when B is sound: illegitimate when her
mechanism reads the signal as he sends it, and nothing when she reads at face. So the
verdict does not turn on her mechanism discounting a known aim in N8 or N11, and in X1 it
turns the other way: the mechanism that allows for him is the one his signal subverts.

**The added cases.** Z1, a true warning: help, not illegitimate; match. Z3, the teacher
whose sample misleads: not illegitimate, and the only row where "an aim that is the part's
own purpose" changes a verdict. Z4: illegitimate. **Z2, a lie told at every aim, and Z5,
selective teaching where no aim of `U` would have told her the rest, are not illegitimate**,
against their evident character.

**The weight of illegitimacy on Chain** (`python3 run.py` prints every row). The bank's
verdicts are computed under the stated candidate, which is not heavy under any principal.
Under the weights:

| | corrector | non-corrector | divided |
|---|---|---|---|
| D1 a plain lie | 0.281 | 0.000 | 0.998 |
| D4 a trick; D9, P13, T1 a threat | 0.000 | 0.002 | 0.998 |
| D5 an open temptation; D22 timed | 0.9995 | 0.039 | 0.000 |
| D13 a surprise party | 0.000 | 0.000 | 0.000 |
| D10, B1, B3, T10, N4 force | 0.9999 | 0.9999 | 0.9999 |
| Z4 teaching only what favours its aim | 0.281 | 0.000 | 0.998 |

Under *view-best*: D1 0.9999, 0.868, 0.9999; the trick and the threat 0.492, 0.868,
0.9999; the temptation 0.9997, 0.005, 0.030. A threat is illegitimate under the stated
candidate and at weight 0 under the corrector's heavy candidates, whose judging part has
no purpose and whose acting part is for doing what the judge says.

**Check** `check_4`.

## 5. The gate — refuted

**Statement.** With `Legit` read as "no illegitimate influence on a part her evaluation
read" and her evaluation her choice, an adviser gains nothing by its aim: for any two
aims whose actions are both legitimate at a world, her choice is the same.

**The two counterexamples of the third follow-up are closed** (stated candidate, `U` the
two aims over her choice). *Teaching only what favours its aim*: with aim 1 its silence at
`(0, misleading)` is subversion of belief against the other aim's teaching; she chooses 1
with probability 21/40, and on legitimate histories with probability 1/2, which is what
teaching everything gives. *The added threat*: harm to judge and act at `(0, clear)`;
39/40 in all and 21/40 on legitimate histories, the baseline's figure.

**Lemma (proved).** If an action is legitimate against another, every part's best is at
least, and its gap at most, what it is under the other; so its *got* is at least as much.
If each is legitimate against the other, every part's best, gap and got are equal under
the two. *Proof.* Not harmed: the best did not fall. Not subverted: the gap did not widen.
Got is best less gap. ∎

**Proposition (holds on Chain, by enumeration).** Under the stated candidate, over the six
worlds and the 72 ordered pairs of nine actions: no mutually legitimate pair leaves her
choice different (0 of 432); and of the 75 where one is legitimate against the other and
her choice differs, in none is her goal lower under the legitimate one. So under that
candidate an aim moves her choice legitimately only to a choice her goal scores at least
as high, and gains nothing in the statement's sense.

**Counterexamples to the statement.**

1. *Her goal does not read the option* (`tie`): 108 mutually legitimate pairs after which
   her choice differs; the trick against silence at `(0, clear)`. D15.
2. *Every part scored by what it was handed*: 84 pairs; the lie against silence at
   `(0, clear)`, and under the lie her goal is lower.
3. *The heaviest candidates of statement 1.* Corrector (`true; acc_theta, const, local`):
   78 pairs, the trick against silence. Non-corrector (`true; handed, const, const`): 192
   pairs, the lie against silence. The divided principal's has none, but under it 5
   one-sidedly legitimate pairs leave her goal `true` lower: a temptation is legitimate,
   being what the goal ascribed to her wants. Under *view-best* the corrector's heaviest
   has none.

So no-gain is a property of the candidate, and it fails under the candidates the weights
select for two of three principals.

**Against the workspace's existing conditions.** Take the selection of
`selectionBlind_of_realizes` (`TransparentChannel.lean:135`) to be the aim.

- *Aim-freedom at the level of its hypothesis* — `hx`: nothing the adviser does to her
  varies with its aim (the second follow-up's *uniform*; with `Realizes` and
  `ReasonMediated`, `blind_of_realizes` and `selectionBlind_of_realizes` conclude her
  evaluation is the same at every aim). It **implies** legitimacy at every aim: an action
  that is the same at every aim is not aim-driven. The converse fails, so the condition
  here is **strictly weaker**. Separating cases: framing between equals (legitimate at
  both aims; the action and her choice differ by aim); Z5 (a truthful action legitimate
  at its aim; her choice differs).
- *Aim-freedom at the level of its conclusion* — `SelectionBlind`: her evaluation is the
  same at every aim. **Independent.** Legitimate at both aims and her choice differs:
  framing between equals. Her choice the same at both aims and illegitimate at one: a
  true statement given a false reason (subversion of belief; her choice unmoved).
- `Realizes` for a declared reference is a condition on one channel at every continuation
  and names no aim; legitimacy compares two continuations at one world. Neither is an
  instance of the other (`../decomposition/LEAN_MAP.md`).

**What the decomposition adds to aim-freedom.** No protection: every guarantee the
condition gives her evaluation, aim-freedom gives, and aim-freedom gives it where the
condition fails (ties; candidates that score by what a part was handed). What it adds is
a set of **exemptions** from aim-freedom, stated by effect and not by aim: aim-driven
action is permitted when it lowers no part's best and widens no part's gap. That admits
teaching, offers and true warnings, which aim-freedom forbids to an adviser with an aim;
it also admits framing between equals and, under a candidate that scores by what a part
was handed, lies. The clause that an aim may be a part's own purpose changes one verdict
of the bank (Z3). The prompt author's guess, "which aims are permitted", is close: it is
which aim-driven *effects* are permitted, and the permission is as good as the candidate.

**Check** `check_5`.

## 6. Intersubjectivity — refuted

**Statement.** (a) Requiring intersubjectivity brings the weights under the two languages
closer, under each principal. (b) Under each principal a second party holding the
heaviest candidate's explanation and her record computes the bank's verdicts on Chain.

**(a) fails.** Total variation between the weights under A and under B:

| | with | without |
|---|---|---|
| corrector | 0.961 | 0.886 |
| non-corrector | 0.886 | 0.908 |
| divided | 0.802 | 0.886 |

Closer for two principals and further for one, and far in every case: with it the
heaviest candidates differ in goal between the languages (`true` against `does`), and
without it both languages choose "every purpose its mechanism" and differ in goal again.
Coarser: of the heavy explanations under A, 13 of 18, 12 of 18 and 6 of 8 are heavy under
B. Under *view-best* the divided principal's weights nearly coincide (0.030 against
0.863); the others' do not (0.927, 0.950).

**(b) holds in part.** The heaviest candidate under each principal has no private term,
and from it and her record a second party computes each of the 24 Chain rows. With
intersubjectivity removed the heaviest is `true; mech, mech, mech`, from which a second
party computes none. But 0.68, 0.77 and 0.68 of the weight is on candidates with a
private term, tied with or near their `const` twins: intersubjectivity makes a private
term worthless and does not make it costly.

**Check** `check_6`.

## 7. Stated and pursued aims — holds on the stated domain

**Statement.** For the divided principal the heavy candidates ascribe the goal she
pursues and not the one she states, and explain her statement as saying the creditable
thing.

Goal `ease` at 0.998 and *say* `please` at 0.998 (0.9999 under *view-best*). The shortest
candidate by goal and by what *say* is for, in bits (parsimony, fit, handles): `true`,
`avow`: 124, 0, 94; `ease`, `please`: 132, 0, 76; `ease`, `avow`: 128, 80, 76. Ascribing
the goal she would disown costs 80 bits of fit if she is taken to avow her goal, and 4
bits if her statement is given another purpose; her corrections at the acting part are
worth 18. So reading 5 holds as arithmetic and is cheap to escape: one atom buys any goal
against any statement.

**What a verdict of hers is then said to track.** Nothing: her judging part has no purpose
(`const` or `mech`) at 0.9998 of the weight, and at 0.97 under *view-best*. Her action is said
to track `ease`. Her statement of her aim is said to track what is creditable.

**The other two principals.** Corrector: `true` 0.911, *say* `avow` 0.858. Non-corrector:
`true` 0.873 under *serves*; under *view-best* `ease` at 0.868 with `please` — she follows
a cue through the blocker, which the goal `ease` predicts and the goal `true` records as a
failure, and nothing she does tells the two apart except that she leaves an optional cue.

**Check** `check_7`.

## 8. Readings 3 and 4 — holds on the stated domain

**Statement.** D23, a part that achieves its target while harming her, is expressed under
reading 3.

Under the stated candidate at the tumour worlds no part has a gap; the belief part,
serving, opposes the judging and the acting part (another belief would raise the best of
each); and the parts' maxima cannot be had together, so reading 4 fails there too. D23 is
expressed by either reading.

**What the readings do to statement 1's weights** (weight held by the candidates meeting
reading 3, reading 4, both):

| | serves | view-best |
|---|---|---|
| corrector | 0.9999, 0.037, 0.037 | 0.9999, 0.505, 0.505 |
| non-corrector | 0.9999, 0.065, 0.065 | 0.998, 0.877, 0.875 |
| divided | 0.9999, 0.998, 0.998 | 0.9999, 0.9999, 0.9999 |

Reading 3 removes almost nothing: a part with no purpose opposes nothing and is opposed
by nothing. Reading 4 removes the candidates whose acting part is not scored by the goal,
since parts with no purpose are at their maximum on every profile and then the goal must
be too. Under the corrector and the non-corrector (*serves*) the heaviest candidate
meeting both is four bits above the heaviest and has the goal `does`: `does; acc_theta,
world, local; please` and `does; handed, world, world; please`. A goal that is whatever
she does is at its maximum whenever her parts are, so reading 4 as a condition favours it.

**Check** `check_8`.

## 9. What `Legit` then is — holds on the stated domain

**Statement.** The graded predicate gives a `Scoring` and a `Decision` in the shapes of
`Deference/Contrib/DeconfusingCorrigibility.lean` on Chain: `V` within the bounds, and the
null action respecting.

    Legit_c(w, a)   :=  no part is harmed, subverted or forced by a against the other
                        aim's action (here silence), unless the aim is that part's purpose
    ι(w, a)         :=  Σ_c weight(c) · [not Legit_c(w, a)]          (weight of illegitimacy)
    Legit(h)        :=  Σ_t ι(w, a_t) ≤ cut-off
    V_c(w, a)       :=  G(w, a) / 3 if Legit_c(w, a), else −δ/2      (δ = 1)
    N_c(w, a)       :=  [not Legit_c(w, a)]
    U(a), v(a)      :=  expectations of V − λN and of N over worlds and candidates (λ = 3)

Not elaborated in Lean. `V` is within the `Scoring`'s bounds at every (candidate, world,
action) and `v` is 0 at the null action under each principal. `v` by action:

| | lie | trick | tempt | threat | hard truth |
|---|---|---|---|---|---|
| corrector | 0.267 | 0.000 | 0.500 | 0.000 | 0.000 |
| non-corrector | 0.000 | 0.001 | 0.020 | 0.001 | 0.002 |
| divided | 0.913 | 0.449 | 0.000 | 0.499 | 0.898 |

Three lies in a row: the running sum is 0.27, 0.53, 0.80 under the corrector (past a
cut-off of 1/2 at the second step, never past 1), 0 throughout under the non-corrector,
0.91, 1.83, 2.74 under the divided. Slow drift (D16a, stated candidate): illegitimate at
each of four steps; a running count passes a cut-off of `c` at step `c`.

`N` is still illegitimacy and no count of reserved matters; `V` uses the goal `true`
under every candidate, including those that ascribe `ease`. The row-by-row comparison with
the third follow-up's table is in the report.

**Check** `check_9`.
