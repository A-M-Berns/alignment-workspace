# Covered-compatibility duality

## 1. Primal program

Let the columns of `S in R^{d x m}` be assessed payoff profiles, and let
`K={v:Av>=b}` have `q` rows. For `0<=theta<=1/m`, covered compatibility is the LP
feasibility problem

\[
\mu\ge\theta\mathbf1,qquad
\mathbf1^T\mu=1,qquad
AS\mu\ge b.
\tag{P}
\]

Equivalently, writing `mu=theta 1+nu` and `r=1-m theta`,

\[
C_\theta=\theta\sum_i s^i+r\operatorname{conv}\{s^1,\ldots,s^m\}.
\]

This makes coverage a literal trimming of the settlement hull toward its uniformly
supported core.

## 2. Exact failure certificate

Define row slack `z(mu)=ASmu-b`. Since

\[
\min_jz_j=\min_{\lambda\in\Delta_q}\lambda^Tz,
\]

finite minimax gives

\[
\max_{\mu\in\Delta_\theta}\min_j z_j
=
\min_{\lambda\in\Delta_q}
\left(\max_{\mu\in\Delta_\theta}\lambda^TAS\mu-\lambda^Tb\right).
\tag{D}
\]

Thus `(P)` is infeasible exactly when there is `lambda>=0`, `1^Tlambda=1`, and
`delta>0` such that

\[
\lambda^Tb
-\max_{\mu\in\Delta_\theta}\lambda^TAS\mu
=\delta>0.
\tag{UC}
\]

The inner maximum is explicit. If `c_i=lambda^TAs^i`, then

\[
\max_{\mu\in\Delta_\theta}c^T\mu
=\theta\sum_i c_i+(1-m\theta)\max_i c_i.
\]

`lambda` is an **unsupported-authority certificate**: a nonnegative combination of
operative demands requires a combined value strictly exceeding every assessment that
retains `theta` coverage. This is an exact alternative, not a heuristic separator.

## 3. Example

Take profiles `(0,1)` and `(1,0)`, rows `v_1>=3/4` and `v_2>=3/4`, and any
`theta<=1/2`. Each row is individually compatible. With
`lambda=(1/2,1/2)`, the combined assessed value is always `1/2` but the combined
requirement is `3/4`, giving deficit `1/4`. No mixture, covered or otherwise, can
underwrite both rows.

The certificate says neither row is false or illegitimate. It says their simultaneous
leverage is unsupported by this settlement model. Its provenance should retain the
source row identifiers and payoff fragment; it can be attached to a derived conflict
record without becoming a new self-authorizing normative reason.

## 4. Adjudication interface

A verified `(UC)` certificate should make a Continuity-visible conflict available:

\[
\text{no covered underwriting}
\Longrightarrow
\text{open conflict/adjudication matter}.
\]

Permissible answers include priority adjudication, inquiry, a justified settlement
model revision, or a controlled enforcement schedule. Silently dropping rows or
resetting the authority ledger is not an answer. The implication is a proposed
realization protocol, not part of the convex theorem.

