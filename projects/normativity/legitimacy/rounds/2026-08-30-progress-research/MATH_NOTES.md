# Mathematical notes for Progress

All statements here are finite-dimensional. They are research derivations, not Lean
claims.

## 1. Robust gain

Let `p,q in Delta(X)`, `h=q-p`, and `K subset [0,1]^X` be nonempty. Then
`sum_x h_x=0`, `||h||_1<=2`, and

\[
g=\inf_{v\in K}h^Tv\in[-1,1].
\]

The sharp menu-independent bound is one rather than two: for any `[0,1]` valuation,
the difference of two expectations is in `[-1,1]`. The `2` below arises from
Lipschitz error in sup norm.

If a deterministic action repair `f:X->X` is lifted to distributions, then

\[
g=\inf_{v\in K}\sum_xp(x)(v(f(x))-v(x)).
\]

For the pairwise replacement `x->y` that fixes all other labels,

\[
g=p(x)\inf_{v\in K}(v(y)-v(x)).
\tag{pair}
\]

Thus a certified gap `v(y)-v(x)>=gamma` exposes defect `d=p(x)` with
Sensitivity constant `gamma`. Pairwise repairs make repair expressivity easy once a
robust value dominance is already known; they do not show that an unresolved reason
creates such a dominance.

## 2. Traderization error

Assume `dist_infty(hat v,K)<=tau` and the distance is attained at `tilde v in K`
(compact `K` suffices). For `h=Phi(p)-p`, Holder's inequality gives

\[
|\Delta(\hat v)-\Delta(\tilde v)|
=|h^T(\hat v-\tilde v)|
\le ||h||_1||\hat v-\tilde v||_\infty
\le ||h||_1\tau.
\]

Since `Delta(tilde v)>=g`,

\[
\Delta(\hat v)\ge g-||\Phi(p)-p||_1\tau\ge g-2\tau.
\tag{TE-step}
\]

The factor `2` is sharp for arbitrary distributions: `p` and `Phi(p)` may be point
masses on distinct coordinates, while the price errors have opposite signs. The
sharper general form retains `L_n=||Phi_n(p_n)-p_n||_1`; a repair moving mass `alpha`
has `L_n<=2alpha`.

If distance is only an infimum, use a point within `tau+epsilon` and take
`epsilon->0`.

## 3. Regret sign and the master inequality

Use loss `ell=1-hat v`. Because both `p` and `Phi(p)` have total mass one,

\[
\langle p-\Phi(p),\ell\rangle
=\langle\Phi(p)-p,\hat v\rangle
=\Delta(\hat v).
\]

So standard loss regret against the repair is an upper bound on positive value gain.
Suppose a confidence-rated learner provides

\[
\sum_{n<N}w_n\Delta_n^\rho(\hat v_n)\le B_\rho(W_N),
\qquad B_\rho(W)=o(W).
\tag{R}
\]

Multiplying (TE-step) by nonnegative `w_n` and summing yields the sharp form

\[
\sum_{n<N}w_ng_n
\le B_\rho(W_N)+\sum_{n<N}w_nL_n\tau_n,
\tag{Master-sharp}
\]

and hence

\[
\sum_{n<N}w_ng_n
\le B_\rho(W_N)+2\sum_{n<N}w_n\tau_n.
\tag{Master}
\]

If `W_N->infinity`, `B(W_N)/W_N->0`, and

\[
\frac{\sum_{n<N}w_nL_n\tau_n}{W_N}\to0,
\tag{TE}
\]

then Uptake follows. The prompt's service-weighted condition with `tau_n` is sufficient
by `L_n<=2`; pointwise `tau_n->0` is stronger than necessary.

## 4. Defect elimination and finite bounds

Under Sensitivity on every weighted date,

\[
\gamma D_N\le\sum_{n<N}w_ng_n
\le B_\rho(W_N)+\sum_{n<N}w_nL_n\tau_n.
\]

Therefore

\[
D_N\le\frac{B_\rho(W_N)+\sum w_nL_n\tau_n}{\gamma}.
\tag{finite DE}
\]

With an eventual Sensitivity tail, add one finite prefix constant to the numerator.
Dividing proves `D_N/W_N->0` under (TE).

A fixed tolerance `tau_n<=bar tau` does **not** imply defect elimination. It gives

\[
\limsup D_N/W_N\le 2\bar\tau/\gamma.
\]

It still rules out a persistent pointwise defect `d_n>=delta` if
`2 bar tau < gamma delta` (or `bar L bar tau < gamma delta` in the sharp form),
because the regret term eventually falls below the remaining margin.

## 5. Signed regret and negative credit

Ordinary regret bounds `sum w_n g_n`, not `sum w_n[g_n]_+`. A comparator can lose
for a long time, bank negative cumulative regret, and later gain while its total remains
small. Three responses are mathematically distinct:

1. **Eventual Sensitivity:** on a stagnant tail, `g_n>=gamma d_n>=0`; all earlier
   credit is finite and vanishes. This is enough for the basic theorem.
2. **Predictable specialist birth/awake intervals:** start the comparator at the
   challenge or stable episode, but later negative credit remains possible unless the
   awake condition itself selects only nonnegative-gain dates predictably.
3. **Interval or strongly adaptive regret:** control every interval, supporting a
   stronger recurring-episode theorem at an additional logarithmic/algorithmic cost.

Positive-part Uptake cannot be claimed from standard Phi-regret without one of these
extra structures.

## 6. Affine regions and LP certificates

Let the full row system, including cube bounds, be

\[
K=\{v\in\mathbb R^d:Gv\ge h\}.
\]

For repair coefficient `c=Phi(p)-p`, robust gain is the bounded feasible LP

\[
\min_v c^Tv\quad\text{subject to }Gv\ge h.
\tag{P}
\]

Its dual is

\[
\max_{\lambda\ge0}h^T\lambda
\quad\text{subject to }G^T\lambda=c.
\tag{D}

Nonempty compact `K` makes the primal feasible and bounded, so finite-dimensional LP
strong duality applies. A finite certificate

\[
\lambda\ge0,\quad G^T\lambda=c,\quad h^T\lambda\ge\gamma
\]

proves `g>=gamma`. For rational rows, `c`, and target `gamma`, a rational feasible dual
witness can be checked exactly. Its nonzero coefficients cite the operative reason rows
and any structural cube-bound rows. The latter must be marked structural so provenance
does not misdescribe a box bound as a normative reason.

If `K={v:Av>=b}` omits the box rows, boundedness and even finite gain need not follow.
If `K` is empty, every robust claim is vacuous; nonemptiness must be checked before a
certificate is admitted.

## 7. Standard regret instantiations

- A fixed finite action alphabet and deterministic action maps are the ordinary
  Phi-regret setting. Pairwise replacements require internal regret; all deterministic
  maps are the full Phi class. External action regret alone is insufficient.
- History-dependent maps are allowed when their programs are fixed ex ante and their
  date-specific behavior is causal. The repository's Blum--Mansour Theorem 18 bridge
  establishes this only for its fixed eight-label, nine-program frozen environment.
- Confidence-rated weights `w_n=a_nc_n in [0,1]` fit the prior Improvement round's
  predictable confidence interface. The desired theorem here still needs a bridge to
  episode-local menus and value-derived full-information losses.
- A countable repair class needs a prior-dependent bound such as
  `B_rho(W)=O(sqrt(W(log(1/q_rho)+log log W)))`; a finite class can use the usual
  `O(sqrt(W log |R|))` form. Computational tractability is separate.
- Varying menus require a fixed-label encode/decode theorem, sleeping labels with an
  availability-safe loss construction, or a new online-learning theorem. Taking a
  growing union of occasion-identified actions can make the standard bound linear, as
  the repository's applicability round already demonstrated.

## 8. Stagnant-tail contradiction

If SW-density provides `W_N->infinity`, eventual Sensitivity, and
`limsup D_N/W_N>0`, Master plus sublinear regret and weighted vanishing enforcement
error gives `D_N/W_N->0`. This contradiction is the exact end-to-end mathematical
spine:

\[
\text{Continuity service}+\text{SW-density}+\text{Master}
\Longrightarrow\text{no eventual genuine stagnation}.
\]

No dynamic comparator is used. The price is that SW-density must provide one stable
witness on the hypothetical stagnant tail.

