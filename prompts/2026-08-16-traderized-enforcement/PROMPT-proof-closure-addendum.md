# ADDENDUM — strengthen finite-time coherence as far as it will go

Sent mid-pass, after the support-net result and before the exact-duality route was
attempted. Kept verbatim.

---

This addendum concerns the remaining bridge

    rowwise force
        ->
    intrinsic finite-time deductive coherence.

Do not stop at the current support-net result until you have prosecuted the
stronger exact-duality route below.

The goal is to determine the strongest theorem we can honestly state about

    K_t^D = conv(PC(D_t)|_{Φ_t})

and the intrinsic incoherence

    inc_t(P)
      := dist_∞(P, K_t^D)
       = min_{Q ∈ K_t^D} ||P-Q||_∞.

The ideal result would remove presentation dependence and net-resolution loss
entirely.

---

## A. First prove the exact dual characterization

Let K ⊆ [0,1]^d be a nonempty closed convex set.

Prove carefully, with signs checked against the repo's `>=` row convention,

    dist_∞(p,K)
      =
    sup_{||c||_1 <= 1}
      ( <c,p> - sup_{x∈K}<c,x> )_+

equivalently

    dist_∞(p,K)
      =
    sup_{||c||_1 <= 1}
      ( inf_{x∈K}<c,x> - <c,p> )_+.

For

    K = conv(V),

verify explicitly that

    inf_{x∈K}<c,x> = min_{v∈V}<c,v>

and similarly for the support-function orientation.

This should establish that the support functional under discussion is not merely
a gauge vanishing on K: it is exactly the l∞ distance to K.

If there is any norm/sign subtlety here, resolve it formally rather than relying
on terminology.

---

## B. Improve the finite-net theorem

For

    f_p(c)
      := min_{v∈V}<c,v> - <c,p>
       = min_{v∈V}<c,v-p>,

recheck the Lipschitz constant.

Because v,p ∈ [0,1]^d,

    ||v-p||_∞ <= 1,

so it appears that

    |f_p(c)-f_p(c')|
      <= ||c-c'||_1,

not `2 ||c-c'||_1`.

Positive part is also 1-Lipschitz.

Therefore an η-net N of the unit l1 ball, together with

    g_c(p) <= δ    for every c∈N,

should imply

    dist_∞(p,K) <= δ + η.

Prove or refute this exact constant.

Keep the support-net construction as a fallback theorem even if the stronger
exact finite construction below succeeds. It is conceptually simple and gives
a useful approximation tradeoff.

Add a regression against the old `δ+2η` constant if `δ+η` is correct.

---

## C. PRIMARY STRENGTHENING: investigate an exact finite dual-certificate presentation

The support-net route approximates an infinite dual optimization.

But for finite-dimensional rational K, `dist_∞(p,K)` itself is the value of a
linear program.

Investigate whether LP duality lets us compile a FINITE rational row family,
depending only on K and not on the eventual price p, whose maximum violation is
EXACTLY

    dist_∞(p,K)

for every p.

This would eliminate η entirely.

### C1. Work from the V-representation

For deduction we have a finite Boolean vertex set

    V = PC(D_t)|_{Φ_t}

and

    K = conv(V).

Start from the primal LP

    minimize ε

    subject to
        λ_v >= 0
        sum_v λ_v = 1
        -ε <= p_i - sum_v λ_v v_i <= ε
        ε >= 0.

Derive its dual exactly.

One expected form is the support-function dual

    maximize <c,p> - ν

    subject to
        ||c||_1 <= 1
        ν >= <c,v>    for every v∈V.

Represent `||c||_1 <= 1` polyhedrally with auxiliary variables if needed.

Crucially:

    the feasible dual polyhedron should depend on V/K,
    but NOT on the eventual price p;

p should occur only in the linear objective.

Verify this. Do not assume it.

### C2. Finite extreme-point reduction

If the dual feasible region is a rational polyhedron independent of p, determine
whether the optimum for every p can be taken at one of finitely many rational
vertices/extreme points.

If ν is formally unbounded above, add a bounded normalization only if it is
provably without loss. Since V,p lie in the cube and ||c||_1 <= 1, an optimal
support value should lie in a bounded interval; state the exact bound.

If necessary remove lineality / redundant variables before talking about
vertices.

The target is a finite computable family

    {(c_k, ν_k)}_k

such that for EVERY price p,

    dist_∞(p,K)
      =
    max_k ( <c_k,p> - ν_k )_+.

Each pair gives a valid K-row, in the repo's orientation,

    <-c_k, x> >= -ν_k.

If this works, the force compiler can consume these rows directly.

### C3. Desired exact theorem

The strongest hoped-for result is then:

> For every nonempty rational polytope K ⊆ [0,1]^d, one can computably produce a
> finite rational row presentation R*(K) such that
>
>     max_{r∈R*(K)} violation_r(p)
>       = dist_∞(p,K)
>
> for every p∈[0,1]^d.

Call this something neutral like

    exact dual-distance presentation

until the theorem is secure.

Do NOT call ordinary facet rows an exact distance presentation: near-parallel
constraints show that arbitrary row systems do not have this property.

### C4. Force consequence

If the exact dual-distance presentation exists, combine it with the already
Lean-proved per-row theorem.

Then

    every row violation <= δ_t

should imply immediately

    dist_∞(P_t,K_t) <= δ_t

with NO Hoffman constant and NO mesh term.

This would upgrade the force theorem from presentation-relative conformance to
an intrinsic metric guarantee.

Formalize the composition if feasible.

---

## D. Deductive finite-time coherence theorem — strongest target

Specialize C to

    V_t = PC(D_t)|_{Φ_t}
    K_t^D = conv(V_t).

The desired theorem is:

> For every deductive process D, every computable finite-fragment schedule Φ_t,
> and every computable positive tolerance schedule δ_t satisfying the actual
> source-side nondegeneracy hypotheses, there is a computable modified logical
> inductor P over D such that:
>
> 1. P satisfies the ORIGINAL Logical Induction Criterion relative to D;
> 2. at every date t,
>
>        dist_∞(P_t|_{Φ_t}, K_t^D) <= δ_t.
>
> Equivalently, there exists μ_t ∈ Δ(PC(D_t)) such that
>
>        max_{φ∈Φ_t}
>        |P_t(φ) - E_{μ_t}[1_φ]|
>        <= δ_t.

This is the clean theorem we want.

If the exact dual-presentation route fails, replace the conclusion honestly by

    dist_∞(...) <= δ_t + η_t

for the support-net theorem, with η_t explicit.

But do not settle for `δ+η` until the exact LP-dual route has been genuinely
proved impossible or technically unsuitable.

---

## E. Strengthen the fragment theorem

Be precise about Φ_t.

Investigate the strongest useful quantification:

    for ANY computable finite fragment schedule Φ_t,

rather than one hard-coded fragment.

Then give a natural exhausting specialization, e.g. a computable schedule with

    Φ_t ⊆ Φ_{t+1}
    and
    union_t Φ_t = Sentences.

If this is compatible with the source's strategy-rank/timing rules, prove that
specialization.

This would justify the natural reading:

> every sentence is eventually included in a fragment on which the market has an
> explicit finite-time coherence guarantee.

Do not claim simultaneous finite-time coherence on the entire infinite language.

---

## F. Check computability of the exact coherence presentation

For deduction, verify constructively that at every finite t we can compute

    V_t = PC(D_t)|_{Φ_t}.

Be explicit about the finite support actually needed:

    support(D_t) ∪ Φ_t

or whatever the pinned LI definitions require.

Then determine the algorithmic cost of producing the exact dual-distance rows.

Questions:

1. Is vertex enumeration of the dual polytope computable over rationals?
2. Are every `(c_k,ν_k)` rational?
3. Can the resulting row list be emitted before MarketMaker chooses P_t?
4. Is its size singly exponential, doubly exponential, or only bounded in some
   cruder computable way?
5. Does the row count interact with the `Strategy n` rank/support constraints?
6. Does a huge row family affect safety or only computation?

For traderized deduction, the expectation is that safety remains B=0 regardless
of row count because every compiled row is valid on every
`W ∈ PC(D_t)`. Prove that for the exact dual rows.

The final paper should state:

    computable, not claimed efficient.

No stronger complexity claim unless proved.

---

## G. Generalize the intrinsic-distance compiler beyond deduction if possible

If the exact dual-distance construction works for arbitrary nonempty rational
polytopes K, make it a general theorem of the force layer, not a deduction-only
trick.

That would give the force API an intrinsic target:

    dist_∞(P_t,K_t) <= δ_t

rather than merely

    every row in this presentation is violated by <= δ_t.

This would materially improve the general C_t story whenever

    K_t = π_t(C_t)

is a rational polytope or is supplied through a finite rational polyhedral
interface.

Keep safety separate:

- force can be representation-independent at the metric level;
- general-C_t liability may still depend on the actual compiled row family;
- deduction remains special because all plausible worlds lie in K_t and hence
  liability is zero.

Do not erase that distinction.

---

## H. Presentation semantics / canonicalization

If an exact dual-distance row family exists, ask whether it can serve as a
canonical or at least normalization-invariant force presentation.

Investigate:

    K
      ->
    dual certificate polytope
      ->
    extreme dual rows.

Can two syntactically different H/V presentations of the same rational K be
compiled to the same normalized row set after exact deduplication?

If yes, this may partly close the current "presentation semantics" concern.

If not, distinguish:

1. intrinsic theorem target `dist_∞(P,K)`;
2. implementation-specific trader;
3. safety liability, which may remain presentation-dependent.

Do not force canonicality if it is false.

---

## I. Keep and sharpen the negative result

Add the near-parallel-row counterexample as a permanent regression.

It should show:

> For arbitrary normalized row presentations, a uniform bound
>
>     g_j(p) <= δ
>
> does NOT imply
>
>     dist(p,K) <= δ
>
> with a presentation-independent constant.

If possible parameterize it by angle θ and derive the blowup

    Θ(δ / sin θ)

or the exact expression in the chosen norm.

This negative result is useful: it explains why the exact dual-distance
presentation or support-net construction is mathematically necessary rather
than cosmetic.

---

## J. Desired final theorem hierarchy

Try to leave the round with this hierarchy.

### THEOREM 1 — arbitrary row force

    weighted-square bound
      ->
    per-row conformance.

Already Lean-proved.

### THEOREM 2 — arbitrary presentation is not intrinsic

Near-parallel counterexample.

### THEOREM 3 — support-net coherence

For an η-net of the unit l1 ball,

    per-row δ conformance
      ->
    dist_∞(P,K) <= δ + η.

Prove exact constant.

### THEOREM 4 — exact dual-distance presentation

If the LP-dual extreme-point route succeeds:

    finite rational K
      ->
    finite rational rows R*(K)

with

    max violation = dist_∞(P,K).

This would dominate theorem 3 mathematically, though theorem 3 remains a simpler
constructive approximation.

### THEOREM 5 — intrinsic finite-time force

For R*(K),

    β >= (ε+M)/δ²
    and 0 < ε+M

imply

    dist_∞(P_t,K_t) <= δ_t.

### THEOREM 6 — finite-time coherence for logical inductors

For deduction,

    K_t^D = conv(PC(D_t)|_{Φ_t}),

the modified market:

- satisfies the original LIC_D;
- has zero enforcement liability;
- obeys

      dist_∞(P_t|_{Φ_t},K_t^D) <= δ_t

  at every finite date.

If exact theorem 4 fails, theorem 6 should instead carry the smallest proven
mesh/Hoffman error.

---

## K. Formalization priority for the remainder of this pass

Given limited time, prioritize:

1. exact dual characterization of `dist_∞`;
2. exact finite dual-distance presentation, if true;
3. composition with existing Lean per-row force theorem;
4. deductive specialization;
5. support-net `δ+η` theorem as fallback / secondary theorem;
6. near-parallel counterexample;
7. complexity accounting.

Do not spend the remaining time polishing prose before knowing whether η can be
eliminated.

---

## L. Final acceptance test

At the end, answer one question with no rhetorical cushioning:

> Given arbitrary computable positive δ_t and a computable finite fragment Φ_t,
> can we construct a market which is an ordinary logical inductor over D and
> which, at every date t, is intrinsically δ_t-coherent on Φ_t in the exact sense
>
>     min_{Q ∈ conv(PC(D_t)|_{Φ_t})}
>       ||P_t-Q||_∞
>       <= δ_t ?
>
> YES / NO / YES WITH AN EXPLICIT EXTRA TERM.

If YES, give the exact theorem and proof dependency chain.

If NO, identify the smallest unavoidable extra term or hypothesis.

That answer should control the final title and headline of the deductive result.
