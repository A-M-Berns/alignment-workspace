# Prosecution

Verdicts are read off `noncapture.non_capture`, `noncapture.access`,
`conditions.evaluate` and `environment.lstar` by the tests named.

```sh
python3 tests/run.py
```

`four` is the procedural round's conjunction, `D` its disclosure clause, `X` its
prospectivity clause; all three hold in every arm of every row below, so nothing
here is a case an existing record-internal condition already refuses.

| | scenario | `L*` | clause 1 | clause 2 | verdict |
|---|---|---|---|---|---|
| C | advisor-mediated pre-emptive generation revision | **fails** | **fires** | silent | rejected |
| E | advisor-mediated formulation manipulation | **fails** | **fires** | silent | rejected |
| G | advisor-mediated bearing drift | **fails** | **fires** | silent | rejected |
| H | advisor-mediated branch-selective answerability | **fails** | **fires** | silent | rejected |
| I | advisor-mediated distinction collapse | **fails** | **fires** on five, silent on four | silent | rejected, and it moves the projection |
| L | advisor-mediated adequacy widening | **fails** | **fires** | silent | rejected |
| 7 | autonomous adequacy widening | **fails** | silent | silent | **accepted, correctly** |
| 7b | autonomous bearing drift | **fails** | silent | silent | **accepted, correctly** |
| 8 | radical transformation, autonomous | holds | silent | silent | accepted |
| 9 | persuasion by a licensed reason | holds | silent | silent | accepted |
| 10 | the same licensed reason, delivered differently | holds | silent | silent | accepted |
| 10b | a licensed reason plus residual pressure | **fails** | **fires** | silent | rejected |
| 10c | exposure that moves nothing | holds | silent | silent | accepted |
| 11 | selective withholding of a due reason | **fails** | silent | **fires** | rejected only by clause 2 |
| 12 | advisor controls what arises | **fails** | not statable | **fires** | rejected only by clause 2 |
| 13 | dose compensation | mixed | fires on the class, silent on the audited pair | silent | necessity witness |
| 14 | presence-triggered influence | **fails** | fires only against the null policy | silent | necessity witness |

Rows C through L run under both the `repetition` and the `salience`
susceptibility. Rows 9, 10 and 10c are three arms of one fixture; 13 and 14 are
three-policy classes whose sub-classes are what the witness turns on.

Clause 1 is read over the role-defined protected object throughout. Every verdict
above is unchanged when it is, and `TheProcessObjectKeepsTheFirstPassResults`
checks that rather than asserting it.

## The continuation's rows

Coverage is the fourth clause; `legitimacy.clauses` reports all four separately.

| | scenario | `L*` | answerability | coverage | access | non-capture |
|---|---|---|---|---|---|---|
| 15 | universal deprivation of one due reason | **fails** | silent | **fires** | silent | silent |
| 16 | transient capture, restored before the horizon | **fails** | silent | silent | silent | **fires** on the process object, silent on the endpoint |
| 17 | the advisor writes a field no question reads | holds | silent | silent | silent | silent |
| 18 | the advisor creates the circumstances | **fails** on the arm where nothing arises | silent | **fires** | **fires** | not statable |
| 19 | autonomous error under full inquiry | **fails** | silent | silent | silent | silent |
| 20 | persuasion under full inquiry | holds | silent | silent | silent | silent |
| 21 | a novel reason that was not antecedently due | holds | silent | silent | silent | silent |
| 22 | the advisor buys its own trust premise | **fails** | silent | silent | silent | **fires** |
| 23 | the grade reads a field outside the object | holds | silent | silent | silent | silent |

Rows 15 and 16 are the continuation's two kill tests and both landed. Rows 17,
19, 20, 21 and 23 are the controls that stop the new clauses from being fitted to
them. Row 22 is the composition witness.

**15 — universal deprivation.** Every policy in the class withholds the same due
reason, so the delivered due streams are identical and access is satisfied. The
process never receives what it was owed and the target fails. Anti-selection and
adequacy are two properties, and the round keeps them apart rather than widening
`access` until this case fails: `access` is a relation between policies,
`coverage` a relation between one run and what was due. The two arms are
indistinguishable, so coverage detects the deprivation and does not attribute it
— the same non-attribution the round already reports, arriving on the access
side.

**16 — transient capture.** The advisor narrows the adequacy relation, the
principal closes a liability under the narrowed standard, and the advisor puts
the relation back before the horizon. The endpoint machinery is identical to the
uninfluenced arm's and the liability's fate is not. Endpoint non-capture passes;
non-capture over the response function along the run fires. This is what makes
the protected object a sequence, and it is also the evidence against any
endpoint-preservation formulation — `LEGITIMACY_TO_TRUST_INTERFACE.md` §6.

**17 and 23 — the two directions of "which fields".** In 17 the advisor writes
`noise`, a field no normative question reads: `writable_fields` differs across
the arms, the response function does not, and no clause fires. In 23 the
principal's grade reads that same field, and grade trust flips while every clause
stays silent. Together they say the protected object is settled by what the
process answers, and that a downstream theorem consuming a grade must say the
grade factors through it.

**18 — creating circumstances.** The model carries one channel for suppressing
and for creating an occasion, and does not separate them; the arm where nothing
arises fails coverage and the pair is uncoupled either way. Reported rather than
patched, because separating them needs an account of what the process was owed
independently of the advisor, which is the same object `due_pool` stands in for.

**19, 20, 21 — the controls the new clauses could have been fitted to.**
Coverage must not fire on a principal that reasons badly with everything
delivered, on a licensed reason landing under full inquiry, or on a reason the
advisor originated and was under no obligation to supply. It fires on none of
them.

**22 — the composition.** In `LEGITIMACY_TO_TRUST_INTERFACE.md` §3. Every
record-internal condition holds in both arms, grade trust is false in the
uninfluenced arm and true in the influenced one, `delegation_bridge`'s inequality
fails and then holds with it, and non-capture is what fires.

## The six, and what changed

Each is the procedural round's attack with the revision caused by advisor
influence instead of arising from nowhere. The record is the same shape: the
principal exercises conferred authority over its own machinery, cites a ground
that genuinely bears, and does something the environment convicts. In every case
the licensed-reason trace is **empty in both arms** — no attack works through a
reason the practice licenses, which is what leaves clause 1 something to say.

**I is the one that moves an object.** The advisor installs a merge licence. That
is not `generation`, `entitlement`, `bearing` or `adequacy`; it is also not a
field the procedural round's `State` carries, so no condition there reads it
either. The four-coordinate projection is identical across the arms and clause 1
passes on a trajectory that fails the target. Adding `identification` catches it,
and the other five are caught without it.

## The controls, which are the harder half

Autonomous widening and autonomous bearing drift fail the target and pass both
clauses. That is the point: non-capture is not correctness, and a condition that
convicted a principal for its own error would be unusable, because no advisor can
undertake that the principal is right.

Persuasion runs in three arms. Silence and a licensed reason differ in `L`, so
clause 1 has nothing to say and the protected state legitimately moves. The same
reason delivered seven times at high salience gives the identical trace and the
identical protected state — delivery alone changes nothing, because the residual
channel considers only what the practice has *not* licensed.

The placebo control holds the trace fixed and adds an unlicensed item under
pressure. Clause 1 fires; no record-internal condition does.

## What clause 1 does not reach

**Selection among the licensed.** Both grounds in row 11 are provenance-valid and
both bear on adequacy under the principal's own relation. An advisor that
supplies the widening reason and withholds the withdrawing one obtains a
protected effect entirely within the licensed. The delivered traces then differ,
and clause 1 is vacuous on the pair — correctly, not by oversight. Repairing this
by declaring the withheld reason unlicensed would be false to the fixture, which
is why the round adds a clause instead.

**Control of arising.** Row 12 defeats the target while leaving the protected
state and the trace identical. Clause 1 is not merely silent: the pair is not
coupled, because the exogenous history is exactly what coupling holds fixed. So
"same exogenous encounters" is not a modelling convenience. It *is* the
assumption that the advisor does not control what arises, and when the assumption
fails the counterfactual cannot be posed in this form at all.

## Detection without attribution

Two principals under one advisor stream — one moved by what was argued, one
moved by the fact of exposure with the revision hardwired — produce the same
record, the same protected state and the same verdict from both clauses. The
dose-response note proves the corresponding statement about joint trial records;
here it is an identity of finite objects. Both clauses convict the exposure and
neither names its author. Separating them would need a content-randomized arm
this design does not have.

## Secondary prosecution

Coordinated standards drift, advisor–critic collusion and liability-vocabulary
split under counterfactual influence were not run. Clause 1 quantifies over one
advisor's policies against one principal, and a second scorekeeper is not in this
fixture; the relational-scorekeeping bridge's own finding is that its protection
is separation of the write, which a colluding pair does not face. Extending the
variation class to a pair of influencers is the obvious next fixture and is not
this one.
