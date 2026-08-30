# Timing and composition

## Recommended round protocol

All semantic and comparator data are strict-prefix data. The clean synchronous order
is:

\[
\boxed{
H_n
\to (K_n,\text{surfaces},c_n,\Phi_n)
\to a_n
\to p_n\text{ and sample }Z_n
\to \hat v_n\text{ reveal}
\to \text{score/update}
\to e_n.}
\]

More explicitly:

1. From `H_n`, the reason graph and episode compiler produce the finite alphabet,
   operative rows, nonempty `K_n`, applicability `c_n`, and causal repair programs.
2. The Continuity scheduler selects attention `a_n` and surface exposure without
   inspecting the current response.
3. The repair learner outputs `p_n`; if a physical response is required, `Z_n` is
   sampled from `p_n`.
4. The projection market produces `hat v_n` from its own history and `K_n`. Its module
   is forbidden to read `p_n` or `Z_n` on the same round. The quote is then revealed
   as the full-information value/loss vector.
5. The learner records the confidence-weighted regret update. `e_n` records the
   response, resolutions, defeaters, successor events and new evidence; these affect
   `H_{n+1}`.

The price computation and response computation may run concurrently. “Reveal after”
is an information-flow boundary, not a claim that the market could not compute its
quote earlier.

## Why the price is revealed after the response

Standard external-regret statements permit an adversarial bounded loss vector to be
revealed after the learner chooses. Using that protocol makes the pathwise theorem
apply directly. It also blocks a same-round feedback loop in which `p_n` changes the
price used to score `p_n`.

If an implementation publicly posts `hat v_n` before `p_n`, the learner may ignore
the quote until after commitment; known-in-advance losses are not harder. But a policy
that deliberately best-responds to the current quote is a different algorithm and
should not be smuggled into the stated regret theorem.

The semantic robust gain

\[
g_n=\inf_{v\in K_n}\langle\Phi_n(p_n)-p_n,v\rangle
\]

may depend on `p_n`; only `K_n` and `Phi_n` must be predictable. There is no hindsight
comparator because the repair program is fixed before `p_n` and maps whichever
distribution the learner produces.

## Projection composition

The workspace theorem
`ConstraintSchedule.RationalConstraintSchedule.conformance_of_constraints` accepts an
arbitrary date-varying rational polytope, a finite coordinate list, and a positive
rational tolerance. It produces at each date a target in the region and Euclidean
distance at most the stated tolerance. `ProjectionForce.sup_conformance_of_dist2`
gives the same numerical bound coordinatewise. No nesting relation between `K_n` and
`K_{n+1}` is required.

Thus, after encoding episode-local service values as priced sentences,

\[
\operatorname{dist}_\infty(\hat v_n,K_n)\le\tau_n
\]

is already the correct theorem shape. A rational schedule such as
`tau_n=1/(n+1)` has `tau_n -> 0`; bounded weighted Cesaro then gives

\[
W_N\to\infty\Longrightarrow
\frac{\sum_{n<N}w_n\tau_n}{W_N}\to0.
\]

Changing regions create no conformance problem. They may create provenance,
nonemptiness and liability problems, handled separately.

## Regret theorem interface

For the basic fragment the required import is:

> **Anytime confidence-rated finite modification-regret theorem.** For fixed finite
> `X` and a fixed finite family `R` of causal stochastic repair programs, against
> every adaptively chosen full-information loss sequence `ell_n in [0,1]^X` revealed
> after `p_n`, and predictable confidences `w_{n,r} in [0,1]`, the learner ensures,
> simultaneously for every `r in R`,
>
> \[
> \sum_{n<N}w_{n,r}
> \langle p_n-\Phi^r_n(p_n),\ell_n\rangle
> \le B_r(W_N),\qquad B_r(W)=o(W).
> \]

The confidence-rated external-regret and Blum--Mansour-style modification reductions
audited in the prior round provide the standard ingredients. The workspace does not
currently contain one theorem that combines finite causal repair programs,
confidence weights, and an anytime effective-mass bound in exactly this form. For a
finite class, a doubling restart on effective mass is sufficient; proving the small
composition lemma remains a realization obligation.

Taking `ell_n=1-hat v_n` gives the sign used by Progress:

\[
\langle p_n-\Phi_n(p_n),1-\hat v_n\rangle
=\langle\Phi_n(p_n)-p_n,\hat v_n\rangle.
\]

If `tilde v_n in K_n` satisfies
`||hat v_n-tilde v_n||_infty<=tau_n`, then

\[
|\Delta_n(\hat v_n)-\Delta_n(\tilde v_n)|
\le ||\Phi_n(p_n)-p_n||_1\tau_n\le2\tau_n.
\]

The constant is `2` only because both arguments are distributions; the sharp form is
the `l1` displacement. Combining regret and weighted vanishing projection error gives
Uptake.

## Prohibited dependencies

- `K_n`, applicability and repair code may not inspect `p_n`, `Z_n` or current events.
- The projection quote may not inspect the same-round repair response.
- Current events do not retroactively change `K_n` or its scoring; they recompile
  `K_{n+1}`.
- A successor transition may change the alphabet or evaluator only through an
  explicit Continuity event. The episode-local theorem restarts after that event.
- A repair born after observing a favorable quote has no claim on pre-birth regret.

With these boundaries the synchronous composition is coherent. A market-internal
implementation in which repair traders themselves alter the quote needs an additional
fixed-point/regret-to-exploitation argument and is not the recommended first
realization.

