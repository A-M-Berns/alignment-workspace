# Coverage contracts

Status: mathematical architecture; unregistered. All new names are provisional.

## 1. Targets

For a certified patch, an exact non-manipulation target is a map \(T:Z\to\mathcal T\)
with a world macrovariable \(\widehat T:\Omega_h\to\mathcal T\) satisfying

\[
\widehat T(\beta(q,z))=T(z)\quad\text{for all admissible }q,z.\tag{TP}
\]

`(TP)` is exact invariance of the estimand under inquiry. It is right for passive
observation and for an active experiment whose target is a stable mechanism or
pre-treatment state. It correctly rejects a query whose target is the downstream
outcome it changes.

It is neither a universal observation/intervention boundary nor sufficient for good
inquiry. A constant or Goodharted receipt satisfies `(TP)` while conveying nothing. A
self-fulfilling test can satisfy `(TP)` for a latent type while failing it for the
realized outcome. Applicability may change even when the target value does not.

The useful family is:

- **exact preservation:** `(TP)`;
- **quotient preservation:** for an equivalence \(\sim\) on target values,
  \(\widehat T(\beta(q,z))\sim T(z)\);
- **transported preservation:** query-specific observations
  \(\widehat T_q:\Omega_h\to\mathcal T_q\) and certified maps
  \(\tau_q:\mathcal T_q\to\mathcal T\) satisfy
  \(\tau_q(\widehat T_q(\beta(q,z)))=T(z)\);
- **potential-outcome preservation:** \(T(z)\) is a response function or mechanism, so
  different realized outcomes under different \(q\) are evaluations of one fixed target.

Applicability is a separate target-relative predicate \(A_c:Z\to\{0,1\}\). A contract
that protects continued relevance requires the same chosen preservation condition for
both \(T_c\) and \(A_c\); otherwise inquiry can make a criticism “inapplicable” by
changing only its classifier.

## 2. Probability-free exposure

Let \(Y:\Omega_h\to\mathcal Y\) be the receipt transcript and
\(Y_q(z)=Y(\beta(q,z))\). For a map \(X:Z\to X_0\), let \(\pi_X\) be its fiber
partition. Write \(\pi\le\rho\) when \(\pi\) is finer than \(\rho\).

For a single executable policy, exact exposure is

\[
\exists q\in Q^{\rm adm},\ \exists d_q:\mathcal Y\to\mathcal T,
\qquad T=d_q\circ Y_q,
\]

equivalently \(\pi_{Y_q}\le\pi_T\).

For a portfolio of queries run on a shared \(z\), let

\[
\mathcal I=\bigvee_{q\in Q^{\rm adm}}\pi_{Y_q}
\]

where \(\vee\) is common refinement. Portfolio exposure is
\(\mathcal I\le\pi_T\). Thus the proposed formula \(\pi_T\preceq\mathcal I\) is correct
only if \(\preceq\) is read as “is refined by”; under the explicit finer-than order here
the inequality reverses.

The static join assumes the same \(z\) can be queried repeatedly, on replicas, or without
state-changing interference. Pairwise separation by different incompatible queries does
not give one-run learnability. The single-patch theory should therefore put complete
sequential/adaptive inquiry policies in \(Q\), let \(Y\) be the full transcript, and use
the single-policy condition above. A policy tree is an implementation of one element of
\(Q\), not a second lifecycle system.

The weakest later quantitative extension is a supplied distribution \(\mu\) on \(Z\)
and either an error bound
\(\mu[d_q(Y_q(z))\ne T(z)]\le\varepsilon\), or a guaranteed information/partition
separation on a contract-specified subset of mass at least \(1-\delta\). Probability is
not needed by the first theorem.

## 3. Registration

Exposure ends at receipt. Let \(J:\Omega_h\to\mathcal J\) be represented
interpretive state, and let \(\operatorname{Rep}_c(J(\omega))\) mean that criticism
identity \(c\) has been registered. The minimal registration interface is the event

\[
\operatorname{Register}_c(\omega):=\operatorname{Rep}_c(J(\omega)).
\]

A route is registration-capable only when it supplies both:

1. target-preserving exposure of a receipt sufficient for the contract's target; and
2. a registration policy or compiler which, when the route is exercised and obtains a
   relevant successful receipt,
   produces \(\operatorname{Rep}_c\) or an explicit pending/non-admission issue.

This is a counterfactual capability, not current registration. Route existence, route
exercise, receipt, and \(\operatorname{Rep}_h(c)\) are four distinct states.

`J` is a world macrovariable for theorem statements. Its realization is ordinarily an
agent-controlled policy component and a normative event compiler. A second patch is
needed only when the theorem compares alternative registration policies. Keeping this
out of the first theorem avoids duplicating the inquiry lifecycle.

## 4. Contract type

A coverage contract at anchor \(a\) is

\[
\sigma=(a,\Gamma,\operatorname{Rel},\mathsf{Adeq},\mathsf{Disp}),
\]

where:

- \(\Gamma\) is a supplied set of stable criticism identifiers;
- \(\operatorname{Rel}_h(c)\) is an externally auditable relevance/applicability
  predicate, transported across ontology changes rather than recomputed solely from the
  current internal vocabulary;
- \(\mathsf{Adeq}_h(R,c)\) checks a certified patch, a target condition, exposure,
  registration, admissibility, and stated resource class;
- \(\mathsf{Disp}_h(c)\) records contract-authorized retirement, exclusion, or transfer.

Criticism \(c\) contains at least its stable identity, target specification, applicability
condition, receipt criterion, registration criterion, and required route-quality class.
It is not merely a sentence already represented by the agent.

Define

\[
\operatorname{Active}_h(c):=c\in\Gamma\land\operatorname{Rel}_h(c)
                         \land\neg\mathsf{Disp}_h(c),
\]

and

\[
\boxed{
\operatorname{Implements}_h(\sigma)\iff
\forall c\in\Gamma,
\operatorname{Active}_h(c)\land\neg\operatorname{Rep}_h(c)
\Rightarrow
\exists R\;\mathsf{Adeq}_h(R,c).}
\tag{IMP}
\]

`Active` may depend on external history, anchored target applicability, and authorized
dispositions. It may not depend only on current internal recognition of \(c\), current
route existence, or the current ontology: each creates the dogmatism loophole.

Universal route existence is appropriate only relative to the finite supplied \(\Gamma\)
and a per-criticism qualitative route standard. Resource feasibility belongs either in
\(\mathsf{Adeq}\) (for a joint schedule certificate) or in a separate portfolio condition;
per-criticism existence alone can overbook mutually incompatible routes. Probabilistic,
sampling, uncountable, and open-ended scopes require a measure/reference class and are
outside this first contract type.

The supplied and historically anchored \(\Gamma\) is the principal genesis-quality
boundary. The theory prevents silent shrinkage of a named scope; it does not derive the
right scope.

## 5. Implementation replacement and scope change

Routes are witnesses, not matters. Replacing \(R_1\) by \(R_2\) preserves the same
contract when both satisfy \(\mathsf{Adeq}\). Shrinking \(\Gamma\), weakening
\(\operatorname{Rel}\), or changing the target transport changes the contract. A
translation \(\sigma\rightsquigarrow\sigma'\) must provide:

1. a total map for every live, undisposed \(c\in\Gamma\);
2. target and applicability transport;
3. no weakening of route quality without an authorized disposition;
4. transfer of pending registration and coverage-failure issues; and
5. a fresh successor issue under Continuity when the entitlement's adjudicative terms
   change.
