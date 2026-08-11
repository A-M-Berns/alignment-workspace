# Remediable failure patterns

## The v1 definition

A **remediable failure pattern** is six things.

1. **A guard.** A predicate over the declared footprint that recognises the
   occasions the pattern occurs on. It reads the record, never the charge.
2. **A recurring actual response.** What the learner does at those occasions.
3. **A lawful replacement.** A response the interface admits at them.
4. **A certificate schema.** Which grounds the replacement cites, and under which
   clause of the interface each is checked.
5. **A saving.** The charge difference at a firing, computed by replay.
6. **An occurrence count.** How many recognised occasions there are, and how many
   the comparator actually fired at.

`RemediablePattern` in `src/regret.py` carries the last three and reports
`uniform_saving` — the single value if every firing saved the same, and nothing if
they did not. A pattern with a varying saving is still a pattern; the report says
so rather than dropping it, because a positive-*rate* statement needs uniformity
and a reader has to be able to see whether it holds.

## The canonical instance

`E4`. Guard: the learner declined and a live interval separating the bound
threshold is on the record for this occasion's target. Actual response: decline.
Replacement: the merits ruling in the certified direction. Certificate: the
interval record, checked under A (available at the prefix), B (it declares
`basis` and names the target), C (undefeated), D (in scope), I (it separates the
threshold in the direction claimed).

At horizon 24 with the pattern on every third occasion: 8 recognised, 8 fired,
saving 2 each, uniform, total 16, rate `2/3` per occasion — and `2/3` again at
horizons 12 and 48.

`E5` is the same construction with the pattern occurring four times whatever the
horizon: total 8 at every horizon, normalized regret `8/T`.

## The consequence theorem, stated and not proved

> **Conjectured.** Let a pattern be recognised on `Ω(T)` occasions of a horizon,
> let a fixed comparator `φ ∈ Φ_law` be admitted on each of them, and let each
> firing save at least `δ > 0` in charge, up to a counterfactual distortion
> bounded by `B` independent of `T`. Then any learner with `R_T(φ) = o(T)`
> against `φ` cannot exhibit the pattern on a positive fraction of occasions in
> the limit.

The argument is one line and the hypotheses are the whole difficulty. If the
learner exhibited the pattern at rate `ρ > 0`, then `φ` would save at least
`ρδT − B`, so `R_T(φ) ≥ ρδT − B`, contradicting `o(T)`.

What that line needs, and where each hypothesis is:

| hypothesis | where it comes from |
|---|---|
| `φ ∈ Φ_law` at each recognised occasion | the certificate check, per firing |
| uniform saving `δ` | `RemediablePattern.uniform_saving`, computed |
| distortion bounded independent of `T` | `COUNTERFACTUAL_CHARGE_INFLUENCE.md` §C — **holds without the solvency coupling, fails with it under a long fence** |
| `R_T(φ) = o(T)` | not established anywhere; this is the next round's subject |

## Self-correction and coverage are different claims

**Self-correction.** *Conditional on a remediable pattern being represented in
Φ_law, a learner with sublinear φ-regret does not exhibit it at positive rate.*
The statement above.

**Coverage.** *Important recurrent remediable patterns eventually enter Φ_law.*
Nothing in this round bears on it, and nothing in this round assumes it.

The gap between them is the whole of the difference between "does not persist in
a failure it can see" and "does not persist in a failure". `Φ_law` here is a
declared finite list; a pattern absent from it produces no regret however costly
and however lawful the repair would have been, and the learner is under no
pressure from this machinery to notice.

Two things follow that a next round should not have to rediscover. Sublinear
φ-regret against a small `Φ_law` is a weak statement, and a round that reported it
without reporting `|Φ_law|` and what is in it would be reporting almost nothing.
And enlarging `Φ_law` is not free: the standard bounds carry `√(log|Φ|)`, so
coverage buys its scope at a rate, which is the honest form of the trade and is
where an inquiry module would have to pay.

## Self-hosting: the ledger and the docket

The hypothesis worth recording, since the interface now makes it checkable: a
`LawfulEditCertificate` plus a recurrence count plus a positive charge
differential is exactly the material of a **remediable-pattern objection** — a
public filing whose grounds are "here is a lawful repair you have declined
repeatedly, and here is what declining it cost."

Every part of that is already typed. The certificate is `src/certificates.py`;
recurrence and saving are `RemediablePattern`; the objection grammar takes
grounds as an identifier, a finite payload, a list of disposition references and
a depth, and computes families from footprints rather than storing them
(`GR-J1`, `GR-J3`). A remediable-pattern filing would declare a footprint over
occasions, responses, reasons and obligations — which is the certifier's
footprint, unchanged.

**No new primitive is proposed and none is needed on the evidence available.**
Whether the generic typed filing suffices is an ontology-audit question, and it
is filed as `PRIORITIES.md` item 31 rather than answered by building something.
The identity being suggested — that the learner's private deviation ledger and
the public docket are two representations of one detected lesson — is a
conjecture, and appears in `THEOREM_LEDGER.md` as one.
