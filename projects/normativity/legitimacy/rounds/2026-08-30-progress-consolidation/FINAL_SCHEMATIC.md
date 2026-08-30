# Final schematic candidate

## Status and scope

This file proposes the basic Progress theorem that a later settlement pass should
freeze. It is episode-local and reason-indexed. It does not prove eventual issue
closure, correctness of the reason, or progress through infinitely many evaluator
eras.

The three levels remain distinct:

1. **Progress meaning:** persistent service cannot retain positive density on a
   defect that a stable eligible reason strictly disfavors.
2. **Eligibility:** Answer-Mode Adequacy supplies a feasible repair and a uniform
   semantic comparison.
3. **Realization:** a compiler, value securities, projection enforcement and regret
   may realize the comparison and Uptake.

## Objects and classifications

Fix a matter `m`, an issue episode `q`, and a historically identified reason
occurrence `r` owned by `q`. Work on a tail on which `q` and the response alphabet
are fixed.

### Inherited theorem: Continuity service

Normative Continuity supplies strict-prefix predicates and attention

\[
\Live_n(m),\quad \Reach_n(m),\quad \Work_n(m),\quad a_n(m)\in[0,1],
\qquad A_N(m)=\sum_{n<N}a_n(m).
\]

Under its wait-responsiveness and non-starvation hypotheses it has already proved

\[
m\text{ live forever}\Longrightarrow A_N(m)\to\infty.
\tag{CS}
\]

Progress consumes this result and does not add a queue or successor relation.

### Definitions

An episode-local response surface has a finite alphabet `X`, a predictable mixed
response `p_n in Delta(X)`, and a predictable exposure/confidence
`c_n(m,r) in [0,1]`. Put

\[
w_n=a_n(m)c_n(m,r),\qquad W_N=\sum_{n<N}w_n.
\]

An Answer-Mode certificate for `r` consists of a predictable feasible repair
`Phi_n : Delta(X) -> Delta(X)`, a defect `d_n in [0,1]`, and a margin
`gamma>0`. With a nonempty admissible region `K_n subseteq [0,1]^X`, define

\[
g_n=\inf_{v\in K_n}\langle\Phi_n(p_n)-p_n,v\rangle,
\qquad D_N=\sum_{n<N}w_nd_n.
\]

A reason is **persistently stagnant on this episode tail** when it remains operative
and undisposed, no recognized answer event occurs, and

\[
W_N\to\infty,\qquad \limsup_N D_N/W_N>0.
\tag{SP}
\]

The last clause is behavioral stagnation, not a disguised gain condition: `d_n` is
specified by the reason's recognized nonresponse modes before values are scored.

### Structural/service assumption: Surface Fairness

While `r` is operative and unanswered, its owning service interface satisfies, for
some `eta>0`, `C<infinity`, and tail start `N_0`,

\[
W_N-W_{N_0}\ge
\eta\bigl(A_N-A_{N_0}\bigr)-C.
\tag{SF}
\]

This is an interface/scheduling obligation. By `(CS)`, it implies Persistent
Relevance `W_N -> infinity`.

### Semantic assumption: Answer-Mode Adequacy

The reason type supplies a stable Answer-Mode certificate such that, on every
exposed tail date,

\[
g_n\ge\gamma d_n.
\tag{AMA}
\]

This is the semantic boundary of basic Progress. A bare question or conflict is not
eligible merely because it is represented. Inquiry, acknowledgment, impossibility,
defeat, action and revision can all be answer modes, but only when the relevant
reason type licenses the strict service comparison.

### Learning assumption: signed Uptake

For every registered eligible repair,

\[
W_N\to\infty\Longrightarrow
\limsup_N\frac{\sum_{n<N}w_ng_n}{W_N}\le0.
\tag{U}
\]

This is the abstract assumption. Markets and regret do not occur in its definition.

## Primary theorem

> **Episode-local Progress theorem.** Fix `m,q,r` and a stable finite response
> surface. Assume Continuity service `(CS)`, Surface Fairness `(SF)`, Answer-Mode
> Adequacy `(AMA)`, and signed Uptake `(U)`. If `m` and `r` remain live and
> operative on the episode tail, then
>
> \[
> \frac{D_N}{W_N}\longrightarrow0.
> \]
>
> Consequently `r` cannot be persistently stagnant on that tail.

**Proof.** `(CS)+(SF)` give `W_N -> infinity`. By `(AMA)`,

\[
0\le \gamma D_N/W_N
\le \frac{\sum_{n<N}w_ng_n}{W_N}
\]

after discarding the finite pre-tail prefix. Uptake makes the right-hand limsup at
most zero. Since `D_N/W_N >= 0`, it converges to zero. This contradicts `(SP)`.

The proof establishes vanishing weighted defect density. It does not establish a
last defective response or eventual issue closure.

## Finite repair-kernel witness lemma

Let `S subseteq X` be defective source modes. For every `x in S`, fix a probability
distribution `mu_x` over recognized acceptable modes, and let a stochastic kernel
`R` fix `X\S` and replace `x` by `mu_x`. Define

\[
u_x=\mu_x-e_x,\qquad d(p)=p(S).
\]

If, for every `v in K` and `x in S`,

\[
u_x^\top v\ge\gamma_x\ge\gamma>0,
\tag{KC}
\]

then the induced repair `Phi_R(p)=pR` satisfies

\[
g^R(p)\ge\sum_{x\in S}\gamma_xp(x)\ge\gamma p(S).
\tag{KW}
\]

Indeed,

\[
\Phi_R(p)-p=\sum_{x\in S}p(x)u_x.
\]

This strictly generalizes the pairwise `x -> y` lemma without moving to arbitrary
nonlinear repairs. More generally, a repair is certificate-realizable whenever
`Phi(p)-p=sum_j d_j(p)u_j`, `d_j(p)>=0`, and the admissible region entails
`u_j^T v>=gamma_j>0`; then `d=sum_j d_j` and `gamma=min_j gamma_j` give
Sensitivity. A generic affine value row need not have this conic repair form.

## Optional realized-response corollary

Suppose an actual response `Z_n` is sampled conditionally from `p_n`, `w_n in [0,1]`
is predictable before sampling, and `W_N -> infinity`. For a defective set `S`,

\[
M_N=\sum_{n<N}w_n(\mathbf1[Z_n\in S]-p_n(S))
\]

is a martingale. Its conditional variance is at most `w_n^2 <= w_n`. The weighted
martingale strong law applies because

\[
\sum_n\frac{w_n}{W_n^2}<\infty
\]

after the first positive mass (grouping increments by the levels crossed by `W_n`
gives the usual telescoping bound). Hence `M_N/W_N -> 0` almost surely. The primary
theorem's mixed defect conclusion therefore implies

\[
\frac{\sum_{n<N}w_n\mathbf1[Z_n\in S]}{W_N}\to0
\quad\text{almost surely}.
\]

This sampling statement is a corollary, not part of the schematic definition.

## Dependency graph

```text
Continuity hypotheses
        |
        v
  Continuity service A -> infinity      Surface Fairness
        |                                  |
        +----------------+-----------------+
                         v
              Persistent Relevance W -> infinity

Answer-Mode Adequacy -> finite kernel witness -> Sensitivity g >= gamma d
                                                    |
Signed Uptake --------------------------------------+ 
                                                    v
                                      weighted defect D/W -> 0
                                                    |
Stagnation Persistence (limsup D/W > 0) ------------X
                                                    |
                                      no persistent stagnant tail
```

`SW-density` should not occur in the primary theorem. It remains a convenient lemma
name for the conjunction `Persistent Relevance + Sensitivity + Stagnation
Persistence` when comparing with the prior round, but it hides the obligations the
settled statement should expose.

