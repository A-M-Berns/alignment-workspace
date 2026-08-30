# REALIZATION — reasons, value securities, traderization, and regret

This document is a candidate realization of `PROGRESS_SCHEMATIC.md`. Nothing here is
part of the meaning of Progress merely because it is convenient for this construction.

## 1. Provenance and current capability

| Component | Repository result actually available | Status relevant here |
|---|---|---|
| Continuity | revision 2, `2026-08-30-normative-continuity-settlement/`, commit `bb741d4`; service theorem and issue succession Lean-verified | upstream and not reopened |
| reason representation | identity-bearing append-only reason multihypergraph/query waist, `2026-08-23-reason-representation/MEMO.md`, landed with `289a07a` | provisional; explicitly lacks typed action targets and the `R -> O` compiler |
| Legitimate Improvement | evidence, uptake, and answerability separated; confidence-rated uptake theorem and retirement accounting, commit `4745c8d` | useful interface; it does not eliminate recurrent defects and leaves evaluator integrity open |
| Phi-regret bridge/learner | fixed eight-label/nine-program bridge, source-derived regret, expected mixed-action recurrent-failure result | valid only in its frozen environment; horizon tuned; learner integration blocked |
| traderized enforcement | affine row and projection enforcers; bounded assessed liability preserves the generalized LI criterion; projection gives intrinsic finite-time distance bounds | enforcement and market safety, not a repair-regret theorem |
| projection enforcement | `2026-08-18-projection-enforcement/`, landed with `289a07a`; Euclidean distance and hence sup-distance at the same tolerance | the clean source of `dist_infty(hat v,K)<=tau` |

## 2. Object map

| Schematic object/condition | Candidate realization | Missing obligation |
|---|---|---|
| matter `m`, service `a_n` | Continuity matter and existing non-starving attention | none at schematic seam |
| service menu `X_n(m)` | finite episode-local semantic labels decoded to available service records/actions | fixed-label or varying-menu encode/decode theorem |
| response `p_n^m` | mixed action of a repair learner on the serviced fraction | composition with attention scheduler and record-producing response |
| admissible `K_n(m)` | nonempty rational polytope in the bounded value-security coordinates | reason-to-row compiler, nonemptiness/conflict disposition, episode provenance |
| valuation coordinate `v(x)` | price of a bounded security `V_(episode,x)` | settlement semantics and an authenticated coordinate map |
| repair `rho` | fixed causal declarative program producing a deterministic map or stochastic kernel on labels | registry, predictability audit, feasibility checker, persistence across menus |
| applicability `c_n` | confidence/specialist gate read from operative reason occurrences at `H_n` | no-laundering anchoring and proof it is known before `p_n` |
| robust gain `g_n` | LP minimum of repair advantage over the reason-generated polytope | dual certificate/provenance object admitted into the reason record |
| Uptake | confidence-rated Phi-regret on losses `1-hat v_n`, plus traderization error | theorem with the exact weights, alphabet, and timing |
| Sensitivity | dual certificate relating robust repair gain to a response defect | normative witness compiler |
| SW-density | stagnant-tail completeness of the reason/repair language | central open bridge |

## 3. Value-security semantics

The weakest useful first semantics is **episode-local anchored score**, not objective
utility or policy value. When issue episode `q` opens, its anchored protocol fixes a
settlement procedure whose possible outcomes assign each service label `x` a bounded
score in `[0,1]`. `V_(q,x)` pays that coordinate. A later evaluator may govern a fresh
successor, but cannot retroactively change `V_(q,x)`.

This is deliberately endogenous. It is enough for a theorem saying the reasoner becomes
responsive to its represented, anchored evaluative constraints. External correctness is
a later Coverage/substantive-validity question.

If direct bounded securities are unavailable, each coordinate can be a priceable affine
combination of the existing sentence securities. The projection-enforcement machinery
already consumes finite price fragments and rational polytopes. What is missing is an
authenticated compiler from an episode's settlement/evaluator record to those priced
coordinates.

## 4. From the reasons multihypergraph to a polytope

An enabled reason occurrence has immutable sources and target, including an explicit
`App(schema,case,stage)` source. A proposed compiler reads only the strict-prefix reason
state, stance, transcript, and episode anchor. Certain typed targets compile to rational
affine rows, for example

\[
v(y)-v(x)\ge\epsilon,
\qquad\text{or}\qquad A_nv\ge b_n.
\]

The result is

\[
K_n(m)=\{v\in[0,1]^{X_n(m)}:A_nv\ge b_n\}.
\]

The multihypergraph supplies identity, applicability, dependency, defeat, and
provenance; it does not itself adjudicate which targets become rows. That compilation
is missing in the current workspace and must not be hidden inside `K_n` notation.

A conflict policy is also required. Contradictory operative rows may make `K_n` empty.
The correct response is a Continuity-visible conflict/inquiry/defeater/successor event,
not explosion by taking an infimum over the empty set.

## 5. Certified reasons for change

For full row system `Gv>=h` and repair coefficient `c`, a nonnegative dual vector
`lambda` satisfying

\[
G^T\lambda=c,\qquad h^T\lambda\ge\gamma
\]

is a finite checkable proof that the operative rows entail robust gain at least
`gamma`. Each nonzero dual coefficient points back to a reason occurrence or a marked
structural cube bound. This makes the proposed insight precise:

> A realized reason for change can be a provenance-carrying certificate that the
> operative constraints entail a robust inequality favoring a feasible repair.

This helps state SW-density, but it does not prove it. The hard step remains showing
that semantic stagnation causes such a certificate to exist for one stable repair.

## 6. Traderized enforcement

Use the projection enforcer when possible. At the realized price vector `hat v_n`, it
can provide

\[
\operatorname{dist}_2(\hat v_n,K_n)\le\tau_n,
\]

and the existing `l^infinity <= l^2` result gives the required sup-distance bound at
the same tolerance. The older row enforcer gives presentation-dependent per-row
violation bounds and would need an additional error-bound theorem to infer distance to
`K_n`.

The Progress interface consumes only the distance certificate and its provenance. The
enforcer's intensity, account, and liability remain realization details.

Weighted vanishing error

\[
\sum_{n<N}w_n\tau_n/W_N\to0
\]

is sufficient. Pointwise convergence is unnecessary. Fixed tolerance suffices only to
rule out defects with a larger fixed certified margin; it does not force normalized
defect to zero.

## 7. Regret realization

Let the learner see loss vector

\[
\ell_n(x)=1-\hat v_n(x)\in[0,1].
\]

For deterministic action map `f` or its stochastic-kernel generalization, the loss
regret equals value gain:

\[
\langle p_n-\Phi_n(p_n),\ell_n\rangle
=\langle\Phi_n(p_n)-p_n,\hat v_n\rangle.
\]

Therefore a confidence-rated Phi-regret bound with confidence
`w_n=a_n c_n` yields the Master inequality in `MATH_NOTES.md` and hence Uptake.

### Exact standard-theorem fit

- Ordinary external action regret is insufficient for action-conditional replacements.
- Pairwise replacements require internal regret; an arbitrary fixed deterministic map
  uses Phi-regret.
- All repairs may be evaluated counterfactually from the same full-information vector,
  so no physical repair scheduler is needed.
- The repair program and confidence must be predictable. The response `p_n` is chosen
  after the weight is known; the loss vector may arrive afterward.
- The prior Improvement construction gives a plausible countable, anytime,
  confidence-rated interface. The earlier Blum--Mansour bridge gives history-dependent
  Phi maps on a fixed finite alphabet but only a horizon-tuned finite class. Neither
  existing artifact by itself proves the exact theorem required here.

### Missing learning lemma

For a fixed episode-local alphabet (or a proved varying-menu bridge), a declared finite
or countable repair class, predictable `a_n c_n`, and arbitrary bounded full-information
loss vectors, construct one learner satisfying

\[
\sum_{n<N}a_nc_n
\langle p_n-\Phi_n^\rho(p_n),\ell_n\rangle
\le B_\rho(W_N),\qquad B_\rho(W)=o(W)
\]

simultaneously for every repair. The construction must state expected mixed-action vs
sampled-path semantics and whether it is anytime.

## 8. Liability and the repair guarantee

The existing Lean theorem `EnforcementPreservation.no_efficient_trader_exploits`
proves:

\[
\text{bounded assessed cumulative liability of the added enforcer}
\Longrightarrow \mathrm{LIC}_L\text{ for the modified market}.
\]

It does **not** prove a quantitative regret bound for repair traders. It bounds the
ordinary TradingFirm's assessed upside and then invokes dominance. Consequently it is
not, by itself, the Master inequality's missing lemma.

There are two implementation routes:

1. **External repair learner (recommended first realization).** A standard adversarial
   regret theorem is pathwise in the bounded loss sequence, so authority enforcement
   may change the prices without invalidating the regret algebra. Existing liability
   preservation is used separately to keep the price process a safe inductor. The
   missing seam is a synchronous composition lemma: authenticated enforced prices form
   the learner's bounded full-information loss vectors, and the learner's response does
   not enter the same quote circularly.

2. **Repair traders inside LI.** A new quantitative bridge is required: compile every
   predictable repair advantage into an efficiently computable, bounded-downside
   trader, and prove that linear weighted repair gain would exploit the market even in
   the presence of the authority enforcer. Existing preservation would then rule it
   out, but converting non-exploitation to a stated `o(W)` regret rate requires more
   than the current theorem.

Thus the exact liability obligation is: bounded assessed liability preserves the
market criterion (already Lean-proved), **plus** either the external synchronous
composition lemma or a new repair-regret-to-exploitation theorem. The workspace does
not currently contain the latter.

## 9. Repair completeness

Repair completeness and normative witness completeness are separate.

1. For fixed finite `X`, all pairwise maps expose any known pairwise robust dominance
   by equation `(pair)` in `MATH_NOTES.md`. All deterministic maps make expressivity
   combinatorially complete for action remappings. This part is comparatively easy,
   though the number of maps is `|X|^{|X|}`.
2. Nothing combinatorial shows that an unresolved reason entails a robust dominance
   over the whole `K_n`, much less one stable across a stagnant tail. Reasons may be
   conflicting, incomplete, incomparable, or directed toward inquiry rather than a
   behavior substitution. This is normative witness completeness and is SW-density.

## 10. End-to-end toy realization

The following model is jointly satisfiable without ad hoc exceptions.

### Continuity trace

- `q_0` is a ready root issue. Its old evaluator supports reason `r_old`.
- At position 1, `r_old` is defeated and `q_0` is explicitly resolved into fresh
  successor `q_1`, anchored to a revised evaluator. This is one genuine evaluator
  revision and one defeated/superseded reason.
- `q_1` remains outstanding and ready forever. Hence its matter remains live,
  `o_n=1`; choose existing feasible attention `a_n=1` for `n>=2`. Thus `A_N->infinity`.

### Values and reason

For `n>=2`, `X={x,y}` where `x` repeats the defective service and `y` incorporates the
persistent repair. Episode-local securities settle to bounded anchored scores. The
persistent enabled reason `r_new` compiles to

\[
K=\{v\in[0,1]^2:v(y)-v(x)\ge1/2\}.
\]

The old contrary row is absent because its occurrence has a recorded defeater. The row
itself is a dual certificate for the repair `f(x)=y`, `f(y)=y`.

### Repair, learner, and enforcement

Let `d_n=p_n(x)`, `c_n=1`, and `w_n=1`. Then

\[
g_n=p_n(x)\inf_{v\in K}(v(y)-v(x))=\tfrac12d_n.
\]

Let traderized prices satisfy `dist_infty(hat v_n,K)<=tau_n=1/(n+1)`. Let a
confidence-rated repair learner have `B(W)<=sqrt(W)` (or simply use a response trace
with the corresponding bound; the point is joint satisfiability). Master gives

\[
\tfrac12D_N\le\sqrt{W_N}+2\sum_{n<N}\frac1{n+1},
\]

so `D_N/W_N->0`. The persistent reason forces defective service mass to vanish, even
though `q_1` need not close. The evaluator revision is explicit; the defeated reason is
represented; the persistent reason has behavioral uptake.

This toy validates composition but not SW-density in general: its witness was built
into the example.

## 11. Realization verdict

The value-security/traderization/regret route plausibly realizes Uptake. Its mathematics
is clean once a nonempty bounded `K_n`, a fixed repair program, and a full-information
alphabet are supplied. The major missing lemmas are, in dependency order:

1. reason occurrence + episode anchor -> authenticated nonempty rational value region;
2. stagnant tail -> stable dual-certified sensitive repair (SW-density);
3. exact confidence-rated Phi-regret for the chosen menu/repair interface;
4. synchronous composition of enforced price production and repair response;
5. if repairs are implemented as LI traders instead, quantitative
   repair-regret-to-exploitation under the existing liability-preserved market.

