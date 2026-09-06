# Finite Progress endpoint

The generic statistic is

\[
 \operatorname{Progress}(T,\Pi)
 =\sum_{e,s}T(e,s)\Lambda_{es}(\Pi_s)+D\left(1-\sum_{e,s}T(e,s)\right).
\]

`e` denotes an evaluated historical obligation occurrence, `s` a service occurrence,
and `Π_s` its one realized response. Different services may contribute different
losses for one exposure. One service uses the same response in every incident edge
certificate. The algebra consumes the evaluated scalar `Λ(e,s)`; the typed response
interface must supply that common-response interpretation.

## Endpoint evidence

PR82's `2026-09-04-normative-inductor-realization/src/realization.py`,
`progress_certificate`, sums each edge's certified bound and adds residual loss;
there is no exposure-only headline loss argument. Its realization document §§8,13
specifies the normalized transport, weighted amplification, error, and residual
used here. This is exact finite implementation evidence plus a paper-derived
contract, not an inference that its semantics are thereby proved.

The wiki's `Progress` page concerns an older fixed-era obligation-weighted endpoint.
That orientation does not identify a general exposure-only loss with the losses of
multiple later responses. The optional exposure-headline theorem therefore has a
distinct endpoint and must state its comparison assumption.

## Theorem ledger

All declarations below are in
`Workspace.Normativity.Contrib.NormativeInductorComposition`; names are provisional.

| Declaration | Full hypotheses and conclusion | Status / scope |
|---|---|---|
| `edge_progress_bound` | Finite `E,S`; `T≥0`; `d≥0`; on positive edges `Λ≤Md+ε`; weighted column sums `Σ_e TM≤Γν`. Then `ΣTΛ+Dr≤ΓΣνd+ΣεT+Dr`. | Lean proof, generic finite algebra |
| `edge_progress_bound_quadratic` | Same positive-edge certificate and `T,d≥0`; `λ≥0`, `Σλ>0`; `λd²≤ρ`; `Γ≥0`; column bound with `ν=λ/Σλ`. Then `ΣTΛ+Dr≤Γ√(Σρ/Σλ)+ΣεT+Dr`. | Lean proof, quadratic uptake specialization |
| `edge_progress_witness` | One exposure/service, `T=1/2`, `Λ=5/8`, `M=1`, `ε=1/8`, `d=1/2`, `λ=1`, `ρ=1/4`, `Γ=1/2`, `D=1`. Instantiates every quadratic-theorem hypothesis. | Lean nonvacuity witness; all three RHS terms positive |
| `edge_headline_separation` | Two equally weighted services with losses `0,1` have average `1/2<1`, the independently proposed headline loss. | Exact Lean witness distinguishing endpoints |
| `progress_bound`, `progress_bound_quadratic` | Existing exposure-headline hypotheses remain; the anchored headline must obey each positive edge's affine bound. | Optional stronger application endpoint, not a core missing bridge |

The basic inequality does not consume a normalized exposure measure, row caps,
nonnegative `D`, nonnegative errors/multipliers, or normalized service weights.
Those are evaluation-protocol conditions where appropriate, not extra algebraic
premises. In particular `Σ_s T(e,s)≤μ(e)` and `Σ_e μ(e)=1` establish `r≥0`;
without them the displayed algebra still holds but its residual need not describe
unserved responsibility. The quadratic theorem derives service normalization.

## Not established

The finite sum theorem does not construct legitimate histories, practical semantics,
adapted transport, affordable intensity, or an uptake bound. It does not identify
price-region feasibility with a jointly certifiable practical response. It proves
neither an exposure-headline bound without its optional comparison premise nor an
asymptotic rate without hypotheses on the three terms.

## Verification and provenance

Command from `lean/`:
`lake env lean Workspace/Normativity/Contrib/NormativeInductorComposition.lean`.
Passed; every new declaration printed only `propext`, `Classical.choice`, and
`Quot.sound`. Existing unused-variable warnings remain in the optional adapter.
The integration round runs the repository axiom audit and registers selected
headlines; this worker does not change the registers. No prompt deviations.
Outstanding maintainer actions: none specific to this worker.

Generator: maintainer-dispatched Codex worker, executor model GPT-6 (OpenAI),
prompt-author model GPT-6 (OpenAI); date 2026-09-06; review status `ci-only`.
Verbatim dispatch: `prompts/2026-09-06-mathematical-consolidation/workers/progress.md`.
