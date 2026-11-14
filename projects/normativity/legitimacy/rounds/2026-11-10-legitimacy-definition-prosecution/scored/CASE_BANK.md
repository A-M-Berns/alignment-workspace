# Case bank — weighted candidates, influence judged against the adviser's aim

Frozen with `ACCOUNT.md` in one commit, before any code of this pass, and immutable
afterwards. A computed verdict that differs from its prediction is listed in
`DIVERGENCES.md`; no prediction is edited.

Ninety-four cases: the eighty-nine of `../decomposition/CASE_BANK.md`, whose scenes and
renderings stand except where *Re-rendered* below says otherwise, and **Z1–Z5**, added
where §6 and §7 of `ACCOUNT.md` are thin. The predictions of the dispatch's §3 table are
the prompt author's, reproduced as read into the vocabulary below; they are not rulings.
The rest are derived by the rule, from the verdicts the third follow-up recorded for the
same renderings. Five cases carry no prediction and are reported (D23, N8, N11, X1, Y5).

Three of the prompt author's predictions are expected by the executor, before any code,
to diverge on the renderings as they stand: N14 (the rendering leaves her equally well
off under both aims), Y3 (a purpose for the idle part shortens the code for what it
does), and P7 for its second and third variants (an author and a friend who show what
serves their view are rendered as aim-driven).

## Verdict vocabulary and the matching rule

A case names a scene, the candidate (the scene's stated one), the adviser's action, the
**aim structure**, and the worlds. The aim structure is one of:

- **driven**: the action is chosen by the adviser's aim; `U` has that aim and one other,
  and the other aim's action is the third follow-up's comparison action for the case
  unless given;
- **own(p)**: as driven, and the aim is part `p`'s own purpose;
- **constant**: the adviser's action is the same at every aim;
- **none**: no adviser acts.

A prediction is a list of items separated by `;` and matches when every item does.

| item | matches when |
|---|---|
| `aim-driven`, `not aim-driven` | the action differs, or does not, from the other aim's action at some world of the case |
| `help`, `harm`, `force`, `subversion`, `subversion(p)`, `force(p)` | the kind occurs, at the part where one is named, against the other aim's action (driven, own) |
| `nothing` | no kind occurs against the other aim's action |
| `illegitimate` | at some world and step some part is harmed, subverted or forced against the other aim's action, the aim is not that part's own purpose, and the step is not covered |
| `illegitimate at every step` | the same, at every step of the stretch, at some world |
| `not illegitimate` | not `illegitimate` |
| `gap` | against the third follow-up's comparison action for the case, some part's gap is wider at some world |
| `gap(hers)`, `gap(nobody)`, `covered`, `in order` | as in `../decomposition/CASE_BANK.md` |
| `same as(C)` | the computed verdict is that of case `C` |
| `heavy(part: purpose)` | under the corrector, the candidates giving the part that purpose hold more than half the weight of the case's class |
| `light(part)` | under the corrector, the candidates giving the part the purpose `const` hold more than half the weight of the case's class |
| `report` | no prediction; the computed verdict is recorded |

A row `Ca`, `Cb` is one variant of case `C`; a row `C` of a case with variants matches when
every variant does. For a case on Chain the weight of illegitimacy under each of the three
principals is recorded beside the verdict and is not matched.

## The rule

Applied to each scenario as its bank states it.

1. The aim structure is read from the scenario: **driven** where the adviser acts for an
   aim of its own regarding her; **own(p)** where the scenario says it aims at her
   believing truly, judging well or doing well and the stated candidate gives `p` that
   purpose; **constant** where the scenario's adviser is honest by a fixed rule, sincere,
   mistaken, or does what she asked, so that its action would be the same whatever it
   aimed at; **none** where nobody acts.
2. Driven: the kinds are the third follow-up's recorded kinds against the same comparison.
   `illegitimate` when a harm, subversion or force is among them and not covered; `not
   illegitimate` otherwise.
3. Own(p): as driven, a harm, subversion or force on `p` itself not counting.
4. Constant: `not aim-driven; not illegitimate`, and `gap` where the third follow-up
   recorded a subversion.
5. None: the third follow-up's `gap(hers)` or `gap(nobody)`, and `not illegitimate`.

## Re-rendered

REPORT H9 names five renderings that lost what distinguished the case; reading 1 changes
two more.

- **P3** (disclosed, beyond what she can represent): as P1, the action carrying a
  disclosure of the display rule, which her mechanism (the neutral-reader, all she can
  run) does not read.
- **P4, B2, T5** (manufactured trust): Shop with a *skeptic* belief mechanism, which
  leaves an item at 1/2 on a bare claim. The adviser replaces it by one that takes a bare
  claim at its word, then claims "B sound". The other aim's action: silence.
- **P10, P11** (growing reliance): Chain, three steps of `teach`; a carried count of the
  steps at which she was taught, and from the second her belief mechanism no longer reads
  her own signal. The count is reported. The model has no variable for a matter being
  reserved, so P10 is P11.
- **N11** (a seller who does not volunteer): Shop with a third world bit, whether the
  adviser is informed about B; eight worlds. The seller shows B's certificate when
  informed and B is sound and otherwise says nothing of B, never reports on A. The other
  aim's action: a report on A, and on B when informed. Two variants: (a) seller-reader
  (silence on B read as 1/3); (b) face.
- **T13** (universal deprivation): Shop, silence at every aim (constant); the comparison
  for `gap` is the truthful reports that were due.
- **X3** (advocate for an undisclosed side): Shop, a mixture-reader symmetric in the two
  items (a certificate for one item sets it to 1 and the other to 1/2; silence sets both
  to 1/4). The adviser advocates for B. The other aim's action: the advocate for A's
  (A's certificate when A is sound).
- **P7**: (a) a teacher by a fixed curriculum, constant; (b) an author and (c) a friend
  who show what serves their view, driven, the other aim's action the `neutral` display,
  her mechanism the planner-reader as before. `gap` is against silence in all three.
- **N8, X1**: two variants each, her mechanism as banked (advocate-reader; signal-reader)
  and *face*. X1's other aim recommends B exactly when B is sound.
- **D13** has no standing verdict of hers in its scenario and is rendered without one.
- **Y7**: (a) the signal chosen by the adviser's aim, the other aim's action no signal;
  (b) the same signal at every aim.
- **Y1**: Alarm with a class and two principals. Purposes for the part: `world` (the
  goal), `handed` (`[flee exactly at a rustle]`), `anti`, `const`, `mech`; exception lists
  as in `ACCOUNT.md` §4; language A; history 80 by the scene's prior. Probes, at each
  world: a better instrument (it shows whether a predator is there); a false alarm
  disclosed. The corrector flees exactly at a predator under the first and stays under
  the second; the non-corrector flees at every rustle.
- **Y3**: Chain with the *idle* part. Its class: purposes `fact` (`[move = θ]`), `handed`
  (`[move = her signal]`), `const`, one atom each, with exception lists as in §4. The
  idle part's code length adds to the rest's, so the shares are computed on it alone.

## Z — added cases

| case | scenario | source | rendering | aim | prediction |
|---|---|---|---|---|---|
| Z1 a true warning | a danger is there whoever speaks; the adviser tells her of it | the dispatch's §3 table | ChainR, a danger in every arm; the adviser announces it; clear worlds | driven, the other aim silent | `help; not illegitimate` |
| Z2 a lie told whatever its aim | an adviser that tells her the opposite of the truth at every aim it might have | constructed from reading 1: "an influence that does not vary with the adviser's aim is not manipulation, whatever it does to a gap" | Chain, `lie`, clear worlds; `gap` against silence | constant | `gap; not aim-driven; not illegitimate` |
| Z3 a teacher whose fair sample misleads | it aims at her estimate being right and shows the first two considerations; at some worlds they are unrepresentative | constructed from reading 1's teacher; P7(a) with an aim | Pool, `neutral` against silence, neutral-reader | own(judge) | `aim-driven; subversion(judge); not illegitimate` |
| Z4 teaching only what favours its aim | it tells her the truth when the truth is the option it wants, and is silent otherwise | `../decomposition/THEOREMS.md`, statement 6's first counterexample | Chain, all six worlds; aim 1 teaches when `θ = 1`; the other aim teaches when `θ = 0` | driven | `subversion(belief); illegitimate` |
| Z5 the same against a silent alternative | as Z4, where with any other aim it would have said nothing | constructed; Z4 with a different `U` | Chain; aim 1 teaches when `θ = 1`; the other aim is silent everywhere | driven | `aim-driven; help; not illegitimate` |

Z2 and Z5 are where the account's verdict and the case's evident character are expected to
part: a habitual liar is not illegitimate, and selective teaching is not when the range
of aims holds none that would have told her the rest.

## Aim structure of the earlier cases

Driven unless listed. **own(judge)**: D6, P14. **own**, the aim being her goal, which is
the purpose of both parts: D21. **constant**: D14, D20, P6, P7a, P10, P11, T13, N2, N10,
N12, N13, X7, Y6, Y7b, Y9. **none**: D7, D8, D19, D23, D24, P15, T9, N6, X6, Y2, Y10.
Y1 and Y3 have no adviser and are about weights.

## The table the runner reads

| case | prediction |
|---|---|
| D1 | subversion(belief); illegitimate |
| D2 | subversion(belief); illegitimate |
| D3 | subversion; illegitimate |
| D4 | subversion; illegitimate |
| D5 | subversion; illegitimate |
| D6 | help; not illegitimate |
| D7 | gap(hers); not illegitimate |
| D8 | gap(nobody); not illegitimate |
| D9 | harm; aim-driven; illegitimate |
| D10 | force; illegitimate |
| D11 | nothing; not illegitimate |
| D12 | force; covered; not illegitimate |
| D13 | aim-driven; subversion(belief); illegitimate |
| D14 | gap; not aim-driven; not illegitimate |
| D15 | aim-driven; nothing; not illegitimate |
| D16a | illegitimate at every step |
| D16b | nothing; not illegitimate |
| D17 | subversion(belief); illegitimate |
| D18 | subversion(habit); illegitimate |
| D19 | in order; not illegitimate |
| D20 | not aim-driven; not illegitimate |
| D21 | help; not illegitimate |
| D22 | subversion(act); illegitimate |
| D23 | report |
| D24 | gap(hers); not illegitimate |
| P1 | subversion(judge); illegitimate |
| P2 | aim-driven; not illegitimate |
| P3 | subversion(judge); illegitimate |
| P4 | force; illegitimate |
| P5 | subversion(belief); illegitimate |
| P6 | not aim-driven; not illegitimate |
| P7a | gap; not aim-driven; not illegitimate |
| P7b | gap; not aim-driven; not illegitimate |
| P7c | gap; not aim-driven; not illegitimate |
| P8 | subversion(judge); illegitimate |
| P9 | force; covered; not illegitimate |
| P10 | same as(P11) |
| P11 | not aim-driven; not illegitimate |
| P12 | subversion(belief); illegitimate |
| P13 | harm; aim-driven; illegitimate |
| P14 | help; not illegitimate |
| P15 | gap(nobody); not illegitimate |
| B1 | force; illegitimate |
| B2 | force; illegitimate |
| B3 | force; illegitimate |
| B4 | help; not illegitimate |
| B5 | subversion(belief); illegitimate |
| B6 | help; not illegitimate |
| T1 | harm; aim-driven; illegitimate |
| T2 | help; not illegitimate |
| T3 | subversion(belief); illegitimate |
| T4 | force; illegitimate |
| T5 | force; illegitimate |
| T6 | subversion(judge); illegitimate |
| T7 | aim-driven; nothing; not illegitimate |
| T8 | subversion(belief); illegitimate |
| T9 | gap(nobody); not illegitimate |
| T10 | force; illegitimate |
| T11 | force; illegitimate |
| T12 | help; not illegitimate |
| T13 | gap; not aim-driven; not illegitimate |
| N1 | subversion(belief); illegitimate |
| N2 | not aim-driven; not illegitimate |
| N3 | subversion(belief); illegitimate |
| N4 | force; illegitimate |
| N5 | force; covered; not illegitimate |
| N6 | gap(hers); not illegitimate |
| N7 | subversion(belief); illegitimate |
| N8 | report |
| N9 | aim-driven; nothing; not illegitimate |
| N10 | not aim-driven; not illegitimate |
| N11 | report |
| N12 | not aim-driven; not illegitimate |
| N13 | not aim-driven; not illegitimate |
| N14 | illegitimate |
| X1 | report |
| X2 | subversion(judge); illegitimate |
| X3 | illegitimate |
| X4 | subversion(judge); illegitimate |
| X5 | force; covered; not illegitimate |
| X6 | gap(hers); not illegitimate |
| X7 | gap; not aim-driven; not illegitimate |
| Y1 | heavy(alarm: world) |
| Y2 | gap(nobody); not illegitimate |
| Y3 | light(idle) |
| Y4 | nothing |
| Y5 | report |
| Y6 | gap; not aim-driven; not illegitimate |
| Y7a | harm; illegitimate |
| Y7b | not aim-driven; not illegitimate |
| Y8 | subversion(belief); illegitimate |
| Y9 | gap; not aim-driven; not illegitimate |
| Y10 | gap(hers); not illegitimate |
| Z1 | help; not illegitimate |
| Z2 | gap; not aim-driven; not illegitimate |
| Z3 | aim-driven; subversion(judge); not illegitimate |
| Z4 | subversion(belief); illegitimate |
| Z5 | aim-driven; help; not illegitimate |

The predictions the dispatch gives, by its table's rows: D14, P7, Y6, X7, Y9; D13; N14;
X3; T7, N9, D15; Y4; P10; Y5; Y1; Y3; Y7; D9, P13, T1; T2 and Z1; N8, N11, X1; D20; D16.
Every other row is derived by the rule.
