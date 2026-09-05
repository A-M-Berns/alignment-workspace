# Normative induction and Progress

**Status: open / unregistered.** The abstract characterization is a paper-level
interface theorem; its fixed-era instances are paper-derived with exact fixtures and a
few kernel-checked lemmas; the general three-term bound is not a Lean theorem.

[Legitimacy](Legitimacy) says what a trajectory owes and to whom. Normative induction
is the quantitative half: given the obligations a legitimate process has incurred, does
the process *learn from them* — does what it owes come to bear on what it does, at a
rate, against an accounting nobody can rig after the fact?

## The obligation-process handoff

Legitimacy exports a **qualitative obligation process**. For every obligation it
determines

- an **identity** — an immutable occurrence fixed at birth;
- an **anchored specification** — what was owed, on the terms it was incurred;
- a **live status** — answered, settlement-discharged, or carried, per
  [Diachronic Answerability](Diachronic-Answerability);
- an **authenticated lineage** — who opened it, what licensed it, what it became.

It does **not** determine numerical importance weights. Which obligations matter more
is not something the legitimacy theory decides from first principles, and an export that
pretended otherwise would let the process that incurs obligations also set the terms on
which it is scored. Qualitative normative status stays separate from quantitative
evaluation, which is downstream and externally declared.

## Live docket versus historical exposure

Two views of the same process, and they serve different consumers.

The **live docket** `Live_n` is what remains owed now: the obligations not yet answered
or discharged, including every successor a disposition opened. This is what a
scheduler consumes — it is where the answering work has to go.

**Historical exposure** records what has entered the process's responsibility at all:
every obligation ever incurred, by its immutable identity, whether or not it is still
live. This is what *evaluation* consumes. A process is judged on what it was
responsible for, and a docket that has been cleared by disposition is not thereby a
clean record.

## Progress is relative to an evaluation protocol

The theory does not decide how legitimately incurred obligations should be weighed
against each other. Instead Progress is stated relative to an externally supplied
**evaluation measure** `μ` over historical exposure, together with a protocol `P` for
producing it:

    Prog_N^{P,μ}

The analogy is a learner evaluated on a declared test distribution. The learner does
not choose the distribution after seeing its mistakes; the evaluation measure is
committed before the responses it scores are observed, or it is not an evaluation. An
application may care about one measure or a family of measures, and the theory's
statements hold for each. What it refuses to do is supply a canonical measure of moral
importance inside the generic framework — that would be a new foundational theory of
correct weighting, and nothing here needs one.

## From obligations to anchored Progress

    O_P  →  service  →  operative uptake  →  practical response  →  anchored Progress

**Service** is the broad relation: an obligation receives the answering work it is
owed, at some date, possibly later than it was incurred. **Scheduled enforcement
intensity** is the resource a particular realization spends to supply service; it is
fixed in advance and is what a scheduler chooses. **Realized corrective force** is what
actually materializes when the reasoner responds; it is endogenous and nobody's to
choose. Reading force as service inverts the sign of learning — a reasoner whose defect
decays under constant intensity looks starved — so the three are kept apart throughout
([Actionability](Actionability-and-Normative-Force)).

Operative **uptake** says that intensity spent against a persisting defect accumulates
work, and that something caps how much work can accumulate without the defect moving.
A **practical response** then turns an operative state into an action, and an
**anchored** loss scores that action on the terms the original obligation was incurred
on, not on whatever the current representation happens to say.

## The endpoint

Under the abstract interface the Progress statistic obeys

    Prog_N^{P,μ}  ≤  Γ_N · Ψ_φ(χ_N)  +  ε̄_N  +  D · r_N .

Three terms, three failures:

1. **Serviced constraints were not taken up, or the amplification was large.** `χ_N`
   is the work ratio — how much intensity-weighted defect survived per unit of
   intensity spent — passed through the coercive uptake modulus `Ψ_φ`; `Γ_N` is how
   much any one service date's response is amplified across the obligations matched to
   it.
2. **Decision or semantic-response error remained.** `ε̄_N` is the transport-weighted
   sum of optimizer error, value-calibration ambiguity, and the drift a reason suffered
   between being owed and being answered.
3. **Legitimate evaluation mass was left unserved.** `r_N` is the share of the
   evaluation measure no admissible service edge reached, charged at the worst loss
   `D`.

The coercive modulus is typed on the bounded defect range: with `φ : [0, D] → ℝ≥0`
the tail quantity is

    φ̌(δ) = inf_{x ∈ [δ, D]} φ(x),   0 < δ ≤ D,

and where an inverse is wanted it is a generalized inverse unless continuity and strict
monotonicity are assumed explicitly.

This is a **sufficiency theorem**, an interface characterization: any realization that
supplies the named witnesses gets the bound. A literal converse is not a current
priority. Within a single era, with one settled semantics, the fixed-era pages —
[Progress](Progress), [Serviceability](Serviceability),
[Liability and affordability](Liability-and-Affordability) — give the instance in
which the first term has a rate and the residual reduces to semantic drift while
waiting.

## The practical-semantics contract is billed, not solved

The step from operative state to anchored Progress passes through *what an action is
worth*, and that is a question about counterfactuals: what would have happened under
the policy the reasoner did not choose. The theory does not attempt a general semantics
of counterfactual policy value. It specifies what such a theory must provide and proves
what follows from the certificate:

- a declared policy or response space;
- authenticated counterfactual value or response semantics for the policies in it;
- calibration and ambiguity guarantees, stated before the response is observed;
- the causal relation between the evaluated responses and the deployed one;
- integrity and non-capture assumptions on the evaluator itself.

Given that certificate, normative induction proves the bound above. Without it, no
theorem here says that a well-behaved operative state implies a good action, and one
exact example on the [Normative Inductor](Normative-Inductor) page shows a state with
zero operative defect whose displayed best action is the uniquely bad one. Logical
Induction in particular does not determine counterfactual policy values; it prices what
settles.

This is an architectural choice, not a gap waiting to be filled. A different decision
theory or a different evaluation ecology plugs into the same interface, and the core
theory stays neutral about which one is right.

## What this does not claim

That obligations are correct. That the evaluation measure is the right one — it is
declared. That any actual reasoner satisfies the interface: the concrete candidate is
the [Normative Inductor](Normative-Inductor), whose end-to-end theorem is conditional.

---

**Evidence.** The abstract contract is maintainer-supplied and not in the repository;
its realization table, theorem spine and the exact final bound are
[`NORMATIVE_INDUCTOR_REALIZATION.md`](https://github.com/A-M-Berns/alignment-workspace/blob/caa3ad083e2d6d8120fbb54120219e907502ad28/projects/normativity/legitimacy/rounds/2026-09-04-normative-inductor-realization/NORMATIVE_INDUCTOR_REALIZATION.md).
The fixed-era instances are in the September checkpoint's
[`CURRENT_THEORY.md`](https://github.com/A-M-Berns/alignment-workspace/blob/939c459974fd1a7365f2c050e883eb1a630123cc/projects/normativity/legitimacy/checkpoint-2026-09-01/CURRENT_THEORY.md).
