# Principal transport

The protected selector is exercised by the future principal, not by the frozen
present one. This states the smallest interface the repair lemma would need to
reach that, what exists, and what does not. **Nothing here is proved.**

## 1. What the repair lemma actually needs

Less than the dispatch's candidate. `REPAIR_LEMMA.md` consumes one object: the
selector `D` at `F(n)`, together with the fact that `A` did not author it. It
does not consume a claim that the *same* principal exercises it.

So the transport statement the round needs is not

```
RecognizedPrincipal(H_0, A, D) + LegitimateTrajectory(H_0 -> H_T)
  -> RecognizedPrincipal(H_T, A, D)
```

but the weaker

```
the trajectory carrying H_0 to H_T is not advisor-authored
  -> D at F(n) is not advisor-authored
```

which is `PRINCIPAL_MEDIATION.md` §1 taken along the run rather than at a point.
That form is checked here, on 27 scenarios. The stronger form is what a
*normative* conclusion would need — why `H_T` still holds the claim `H_0` held —
and it is the one that is missing.

## 2. Inputs

| input | what it must say | status |
|---|---|---|
| non-capture along the trajectory | at equal licensed-reason traces the protected process, hence the selector, is invariant at **every step** | exists; `noncapture.non_capture` over `response.process_projection`, composed here |
| coverage | every due reason arrived on the arm | exists; that round's fourth clause, and it is the only one a single run determines |
| the selector factors through the protected process | `D = f(Z)` | premise, with a necessity witness |
| normative learning | how the principal's substantive responses may change | exists as an interface, `projects/normativity/notes/NORMATIVE_LEARNING_INTERFACE.md`; **not** a source of standing |
| role continuity | why the principal role stays attached across the change | **missing** |
| a transfer operation | what it is for the role to move, and what makes a move valid | **missing**; the ledger has `transport`, which carries an account through a renaming and settles nothing about whether the renaming was permitted |

Three roles stay separate and the round keeps them separate. Normative learning
explains how the principal's responses may improve. Counterfactual legitimacy
says the trajectory is not advisor-authored through residual channels. Transport
would say why the role remains attached through that change. **Learning does not
generate standing**, and nothing here suggests it does.

## 3. The laundering attack

`A` manipulates `H`, and `H` then performs a formally valid transfer of
principalhood to `A`.

**A provenance rule reading only the final transfer certifies it.** The finite
witness is that round's `transient_capture`: an advisor moves a standard, lets a
liability close under it, and restores the standard before the horizon. Every
endpoint projection is identical across the two arms and the processes differ, so
an endpoint rule cannot distinguish a transfer made under capture from one made
freely. Process non-capture refuses it. This is the same reason that round takes
its protected object along the run, arriving at the transfer question.

**The ledger refuses a second form of it.** Transporting the claimant role onto
the debtor does not let the debtor discharge itself: the no-self-release check
reads the debtor field and fires first. So "become the principal, then release
yourself" is closed structurally rather than by a rule about transfers.

**What neither refuses** is a transfer produced by licensed persuasion. The
advisor supplies reasons the principal is entitled to weigh, the principal is
moved by them, and hands over the role. Non-capture is silent because the traces
differ; coverage is silent because nothing due was withheld. This is the same
residue as that round's selection-among-licensed-reasons attack, where clause 1
is silent and clause 2 fires only if something was withheld — and here nothing
was.

## 4. Verdict

**Transport is blocked, on a residue that is not new.** The non-authorship half
is available and composed. The role-continuity half needs an object nothing in
the repository carries, and the attack that decides it is legitimate persuasion
toward transfer, which is exactly the case the legitimacy interface declines to
forbid and should decline to forbid.

The repair lemma does not wait on this. It consumes the non-authorship half only.
