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
The fixed-era instances — one era, one settled semantics — are on
[Progress](Progress), [Serviceability](Serviceability) and
[Liability and affordability](Liability-and-Affordability), and are realization
material rather than part of the generic theory.
