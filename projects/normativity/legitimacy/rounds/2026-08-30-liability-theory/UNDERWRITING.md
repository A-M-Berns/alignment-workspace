# Underwriting

## 1. Abstract lemma

Let `E=(E_1,...,E_m)`, assume `E_i<=U`, and let `alpha` be a probability vector with
`alpha_i>=theta>0`. If

\[
\Lambda_\alpha(E)=\sum_i\alpha_iE_i\ge-S,
\]

then, for every `i`,

\[
E_i\ge-\frac{S+(1-\alpha_i)U}{\alpha_i}
\ge-\frac{S+(1-\theta)U}{\theta}.
\tag{UW}
\]

Proof: isolate `alpha_i E_i` and upper-bound all other coordinates by `U`. The
constant is sharp given only these hypotheses. This abstraction earns its keep: it
separates the market-supplied upper envelope, the coverage functional, and the
potential deficit. Common-Mixture Affordability is `(UW)` with `S=0`.

An ex post choice of `alpha` and `S` would be vacuous. A substantive underwriting
certificate must be fixed or certified from public schedule/settlement geometry,
independently of the realized authority loss it is supposed to bound. Projection
compatibility supplies exactly such a certificate.

## 2. Meaning of theta

`theta` is the minimum coefficient assigned to each relevant payoff profile by the
underwriting functional. Mathematically it is simultaneously:

- a coverage margin;
- the reciprocal scale of the worst cross-profile leverage permitted by the proof;
- a robustness margin against concentrating all underwriting weight away from the
  world where authority loses.

It is only an “anti-dogmatism” or “standing” margin in this limited assessment sense;
it is not Continuity standing or moral status. As `theta` tends to zero, a potential
can offset arbitrarily large loss at one profile with bounded gain elsewhere, and the
bound diverges.

For binary settlements `{0,1}` and point peg `K={c}`, compatibility uniquely fixes
`mu=(1-c,c)`, so

\[
\theta=\min(c,1-c).
\]

The center has `theta=1/2`; a peg at `epsilon` has `theta=epsilon` and inverse-margin
exposure. For an interval `[lo,hi]`, optimal coverage is
`1/2-dist(1/2,K)`, whereas PR50's flow margin is `min(lo,1-hi)`. They agree for point
pegs but not in general.

## 3. Static common-potential theorem

For a stationary region `K`, `K cap C_theta(Omega)` provides a barycenter `sbar`.
Every projection trade has nonnegative value at `sbar`; sums retain that sign. With
the LI upper envelope `U=3`, `(UW)` yields

\[
E_N(\omega)\ge-3(1-\theta)/\theta
\]

at every horizon and profile. Several coordinates and simultaneous rows cause no
additional accounting term. Dimension matters only through achievable coverage;
with `2^d` independent binary profiles, uniform coverage may be `2^{-d}`.

## 4. World inclusion and weaker support

If every `S(omega)` lies in every contributing region, each world evaluation itself
underwrites the projection and liability is zero. Covered underwriting is strictly
weaker: individual worlds may violate the rows while a covered barycenter satisfies
them.

Support-local coverage is legitimate only after quotienting by authority payoff
profiles and retaining live representatives to which the TradingFirm floor applies.
Dropping a profile merely because its weight is inconvenient changes the assessment
obligation rather than proving affordability.

