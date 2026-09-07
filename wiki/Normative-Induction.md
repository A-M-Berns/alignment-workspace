# Normative induction and Progress

**Status: canonical.** The Progress statistic, the edge-local practical certificate,
and the finite three-term bound on the accounted export are Established
`lean-proved`, with a nonvacuity witness in which all three terms are positive. The
practical semantics and the evaluation protocol are typed inputs.

[Legitimacy](Legitimacy) says what a trajectory owes and to whom. Normative
induction is the quantitative half: given the obligations a legitimate process has
incurred, does what it owes come to bear on what it does, at a rate, against an
accounting nobody can rig after the fact?

## The handoff

Legitimacy exports the **accounted obligation state** `O_P`: the exposed occurrences
with their immutable anchors, the live docket, and the proof-relevant account of each
occurrence. It exports no weights, importance, service intensities, probabilities,
securities or market geometry. Which obligations matter more is decided downstream by
an evaluation protocol the application declares, so that the process which incurs
obligations cannot also set the terms on which it is scored.

Two views of the same state serve different consumers. The **live docket** is what
remains owed now — what a scheduler consumes. **Historical exposure** is everything
that ever entered the process's responsibility — what evaluation consumes. A docket
cleared by disposal is not a clean record.

## The evaluation

An **evaluation** of `O_P` is indexed by the state and reads two of its fields: the
exposed occurrences and their anchors. It never inspects the account. It declares:

- an **evaluation measure** `μ` over exposure and a **transport plan** `T` from
  exposures to service occurrences, both committed before the responses they score
  are observed — a learner does not choose its test distribution after seeing its
  mistakes;
- for each service occurrence `s`, the **one response** `Π_s` actually realized there
  from the market state, and a public **operative defect** `d_s`;
- an **anchored loss** `Λ_{r,s}` of a response, as a function of the *anchor* `r` —
  two occurrences with one anchor get one loss and two transport rows, so multiplicity
  is in `μ` and `T`, never in the loss;
- a worst loss `D` and the certificate constants.

## The statistic

    Progress = Σ_{e,s} T(e,s) · Λ_{anchor(e), s}(Π_s)  +  D · (1 − Σ_{e,s} T(e,s))

The transport-weighted loss of every served edge against the response realized at its
service, plus the unserved evaluation mass charged at the worst loss. This is the
realization round's statistic. An exposure-level headline loss with one number per
exposure is a different endpoint — an exact witness separates the two — and the
theorem about it is an optional corollary, not the canonical bound.

## The practical certificate

For each edge with positive transport,

    PracticalCert(e, s, Π_s):   Λ_{anchor(e), s}(Π_s)  ≤  M_es · d_s + ε_es .

One service occurrence realizes one response, and every exposure transported to it
certifies against that same response. This is where joint practical-response
compatibility lives: two obligations can share a feasible operative region while no
single response is adequate for both, and then one of them is not certified and its
mass is residual. Value correspondences, approximate optimizers, finite policy menus
and adequate-set semantics are sufficient ways to *produce* the certificate; none is
public structure.

## The bound

Under nonnegative transport and defect, `PracticalCert` on every served edge, the
**uptake certificate** `λ_s d_s² ≤ ρ_s` for the intensity `λ_s` spent at each service,
and the **amplification bound** `Σ_e T(e,s) M_es ≤ Γ · λ_s / Σλ`:

    Progress  ≤  Γ · √(Σ_s ρ_s / Σ_s λ_s)  +  Σ_{e,s} T(e,s) ε_es  +  D · r ,

with `r = 1 − Σ T` the residual mass, which lies in `[0, 1]`. Three terms, three
failures: serviced constraints not taken up or amplified; decision or semantic error
in transported responses; evaluation mass left unserved.

This is a sufficiency theorem. Any realization that supplies the named certificates
gets the bound.

## The decision interface

**Status: the static interface is Lean-proved and unregistered; the margin is a typed
input with two routes; the dynamic case is open.**  What the bound above asks of decision
theory is the practical certificate on each supported edge, and the adequate-set route
factors that into a semantic half — adequate responses cost at most `ε_ad`, every
response at most `D` — and one decision-theoretic half: the realized response
distribution's mass off the adequate set is affine in the public defect.  The static
bill is therefore **a continuity/coupling condition, not expected-utility
maximization.**

    adequacy semantics → compiled region → market proximity → sound stable adapter
        → PracticalCert → Progress

- **Adapter abstraction.**  Any map from displayed scores to response distributions
  that is *sound* at a region point (mass off the adequate set at most `θ`) and
  *Lipschitz* in the scores at rate `κ` per unit sup-distance satisfies the coupling,
  and then the certificate with `M = D κ`, `ε = ε_ad + D θ`.  Every arrow from the
  adapter to Progress is a literal hypothesis match.
- **Soft gate, one realization.**  Weight each response by a ramp of width `δ` on its
  adequacy score above a threshold `τ`, times a task preference, and normalize.  With
  the region excluding inadequate responses at `τ` and a margin of adequate preference
  mass `W` above `τ + 2δ`, the mass off the adequate set is at most the inadequate
  preference mass over `W`, per unit of defect relative to `δ`.  The natural hard gate
  — task-argmax over responses priced above `τ` — is sound and has no Lipschitz
  constant: at every positive defect it can execute an inadequate response with mass
  one.  Continuity is the whole decision-theoretic content.
- **Positive margin is semantic or epistemic, not decision theory.**  Region soundness
  excludes; it marks nothing.  The margin comes by route A — the compiler positively
  marks an adequate response at the region point, a completeness condition — or by
  route B — the market displays one on its own, which a learning theorem about prices
  could supply asymptotically and without rate.  Both routes are pointwise at the
  occasion and apply to adequacy that is derivable or externally certified.  Adequacy
  known only through later settlement is outside the static theorem; the bridge from
  average calibration to average inadequate-action mass is not proved.
- **Charged through amplification.**  The constant `M = D κ` enters Progress through
  the amplification hypothesis, so the exact end-to-end condition is the existing one;
  the local reading is that market error must shrink relative to the certified margin
  with the inadequate-to-adequate preference-mass ratio controlled.
- **Not part of the definition.**  The soft gate is a realization of the adapter
  `Pi`, not a component of the Normative Inductor; the Inductor's substrate and the
  evaluation are unchanged by it.  Task competence inside the adequate set is the
  application's; a bounded-inductive-rationality learner on the gated sequence
  supplies it for a supplied decision-problem sequence.
- **Inquiry.**  When no response is confidently adequate the gate returns an inquiry
  response, charged at `D` through the residual and never a violation; in the Lean
  this is a wrapper silent under margin, and the cleaner semantics compiles "inquiry is
  adequate" from a certified conflict so that inquiry is an ordinary response.
- **Open.**  When an admissible act changes the next admissible set, a myopic gated
  learner is safe and not competent against legitimate continuation policies; bounded
  competence under an endogenously changing admissibility process is the next
  problem ([Corrigibility](Corrigibility)).

## What is billed

The evaluation protocol — `μ`, `T`, `D` — is the application's. The truth of each
`PracticalCert` is the practical-semantics contract: that `Λ` scores the response
against the immutable anchor rather than a later substitute, that the map from the
realized response to the anchored response space has the declared causal meaning,
and the inequality itself. Logical Induction prices what settles; it does not
determine counterfactual policy values, and the theory does not derive them from
market conformance.

---

**Evidence.** The evaluation on the accounted state, `PracticalCert`, the uptake
package and the bound are
[`NormativeInductionInterface.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/c24159764974232dfd5b47a10b671f12d6f9c244/lean/Workspace/Normativity/Contrib/NormativeInductionInterface.lean),
registered as `ni.progress-bound`; the finite algebra and the endpoint separation are
[`NormativeInductorComposition.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/c24159764974232dfd5b47a10b671f12d6f9c244/lean/Workspace/Normativity/Contrib/NormativeInductorComposition.lean),
registered as `progress.edge-bound`, `progress.edge-bound-quadratic` and
`progress.headline-separation`. The minimal certificate and the joint-compatibility
analysis are the practical certificate round's
[`CERTIFICATE.md`](https://github.com/A-M-Berns/alignment-workspace/blob/c24159764974232dfd5b47a10b671f12d6f9c244/projects/normativity/legitimacy/rounds/2026-09-05-practical-certificate/CERTIFICATE.md)
and
[`JOINT_COMPATIBILITY.md`](https://github.com/A-M-Berns/alignment-workspace/blob/c24159764974232dfd5b47a10b671f12d6f9c244/projects/normativity/legitimacy/rounds/2026-09-05-practical-certificate/JOINT_COMPATIBILITY.md).
The decision interface — the adapter abstraction, the soft gate with its sharp constant,
the hard-gate witness, the two margin routes and the inquiry wrapper — is
[`GatedChoice.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/ab260c0eade2f39de7c06a5ac58649945d66c9ab/lean/Workspace/Normativity/Contrib/GatedChoice.lean),
with the register in the decision-theory-bill round's
[`DECISION_THEORY_BILL.md`](https://github.com/A-M-Berns/alignment-workspace/blob/ab260c0eade2f39de7c06a5ac58649945d66c9ab/projects/deference/rounds/2026-09-06-decision-theory-bill/DECISION_THEORY_BILL.md)
and
[`NORMATIVE_CHOICE_THEOREM.md`](https://github.com/A-M-Berns/alignment-workspace/blob/ab260c0eade2f39de7c06a5ac58649945d66c9ab/projects/deference/rounds/2026-09-06-decision-theory-bill/NORMATIVE_CHOICE_THEOREM.md);
its declarations are unregistered.
The fixed-era instances — one era, one settled semantics — are on
[Progress](Progress), [Serviceability](Serviceability) and
[Liability and affordability](Liability-and-Affordability), and are realization
material rather than part of the generic theory.
