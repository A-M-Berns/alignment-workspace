# Theorem Spine

The program's mathematical results in their most mature form, stated at theorem level
with hypotheses, conclusions, and the strength each one actually has.  The conceptual
pages ([Legitimacy](Legitimacy), [Integrity](Integrity),
[Openness, Coverage and Non-Capture](Openness-Coverage-and-Non-Capture),
[Normative Induction](Normative-Induction), [Deference](Deference),
[Corrigibility](Corrigibility), [Continuation BRIA](Continuation-BRIA)) say what each
result means for the question that motivated it; this page says what is proved.

The presentation follows the maintainer's manuscript *Legitimate Evolution and Normative
Induction* (draft 0.4, September 2026), which is the most mature single statement of the
spine, and the repository's consolidated results, which are what the manuscript's Lean
citations resolve to.  Where the two differ in form, the repository's declaration is the
statement of record and the manuscript's numbering is given for orientation.

## Reading the labels

| label | meaning |
|---|---|
| **registered** | a Lean declaration listed in a claims registry ([normativity](https://github.com/A-M-Berns/alignment-workspace/blob/aed09a697121e1d575473e3e7d87058ea85a49a3/projects/normativity/CLAIMS.md), [deference](https://github.com/A-M-Berns/alignment-workspace/blob/aed09a697121e1d575473e3e7d87058ea85a49a3/projects/deference/CLAIMS.md)) at class `lean-proved`; the registry row, not this page, is the record |
| **LEAN** | sorry-free, audits to `propext`, `Classical.choice`, `Quot.sound`; deliberately unregistered because no filed priority is answered at registration strength |
| **FIX** | an exact rational fixture in a round's `tests/`, exhaustive where the statement is finite |
| **paper-derived** | proved in a maintainer note or a round document by ordinary mathematics, not mechanized; the checkpoint [status ledger](https://github.com/A-M-Berns/alignment-workspace/blob/aed09a697121e1d575473e3e7d87058ea85a49a3/projects/normativity/legitimacy/checkpoint-2026-09-01/STATUS_LEDGER.md) governs how strongly each is held |
| **PAPER** | imported from a published source ([Sources](Sources)) and not re-proved here |
| **conditional** | a theorem whose hypotheses no concrete realization is known to inhabit simultaneously |
| **EXT** | an interface contract: the supplier's obligation, not a theorem |
| **OPEN** | filed and not settled |

Every result below is one of these.  Nothing is upgraded by appearing here.

## 1. The account calculus and Integrity

The qualitative spine works on *accounts*: proof-relevant trees whose leaves are live,
answered, or closed occurrences of anchored obligations, and whose internal nodes are
authenticated transformations.  Lean:
[`OccurrenceIntegrity.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/aed09a697121e1d575473e3e7d87058ea85a49a3/lean/Workspace/Normativity/Contrib/OccurrenceIntegrity.lean),
[`LegitimateEvolution.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/aed09a697121e1d575473e3e7d87058ea85a49a3/lean/Workspace/Normativity/Contrib/LegitimateEvolution.lean).

**Theorem 1.1 (Faithful substitution; manuscript 7.1).**  For an account `t`, a
substitution `ρ` of replacement accounts for its live ports, and any assignment `v` of
resolution witnesses to the live ports of the result,

```
(t.subst ρ).evaluate v  =  t.evaluate (fun p => (ρ p).evaluate v)
```
— the later account evaluates back to the earlier one through the transport of live
witnesses.  `Program.evaluate_subst`; **registered** `legitimacy.faithful-carry`.

**Theorem 1.2 (Receipts are immutable under revision; manuscript 7.2).**  Under the same
substitution the terminal receipts of the result are exactly the prior terminal receipts
plus those introduced inside the replacements:

```
(t.subst ρ).terminals  =  t.terminals  +  Σ_{p ∈ t.livePorts} (ρ p).terminals
```
so no prior receipt is removed or modified.  `Program.terminals_subst`; **registered**
`legitimacy.receipts-immutable`.

**Theorem 1.3 (Answerability Conservation from Integrity; manuscript 8.3).**  An
*Integrity evolution* `ev : Evolution O₀ O₁` between accounted states is a chain of
transitions each of whose target account is the propagation of its source through
explicit replacement accounts, with intermediate states part of the object.  Then
`Conservation O₀ O₁` holds, which is the conjunction

1. *exposure*: every obligation exposed in `O₀` is exposed in `O₁`;
2. *receipts*: for every exposed `o`, the terminal receipts of `O₀`'s account for `o` are
   a sub-multiset of those in `O₁`'s;
3. *faithful carry*: there is a transport of live witnesses under which every later
   account evaluates back to the earlier one.

`Evolution.conservation`; **registered** `legitimacy.evolution-conservation`.  The target
account is a *function* of the source account and the certificate
(`Evolution.propagate_toSegment`, **registered** `legitimacy.propagate-to-segment`): there
is no freedom to choose it.  Composition (manuscript 8.4) is `Evolution.trans`.

**Corollaries 1.4 (No Semantic Laundering, No Retroactive Strengthening; manuscript
6.2, 6.3).**  A non-bottom portion of an obligation's anchor neither validly answered nor
validly closed remains represented in the join of current carrier loads; additional
content cannot be attributed to a historical obligation by revising its representation.
Both are read off Theorem 1.3 at the semilattice level.  **paper-derived**: the
semilattice formulation with anchored loads, slice-faithful interpretation and the
generalized transfer identity

```
⊔_{x∈P} λ_n(α,x)  =  u_ans ⊔ u_cls ⊔ ⊔_{y∈Q} λ_{n+1}(α,y)
```
(manuscript 6.1, proved by finite induction over transitions) is not yet one Lean
declaration in the occurrence-indexed calculus.

**Witness 1.5 (identities do not collapse; manuscript §6.1, counterexample 19.1).**  Two
occurrences with one anchor, one answered and one carried by a single transition, have
fates `{answered}` and `{live}`.  `Witness.distinct_fates`; **registered**
`legitimacy.multiplicity-witness`.  Since `a ⊔ a = a`, one semantic value cannot stand
for two historical debts; historical identity is prior to extensional identity.

## 2. Robust Openness

Lean:
[`NonCaptureCertificate.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/aed09a697121e1d575473e3e7d87058ea85a49a3/lean/Workspace/Normativity/Contrib/NonCaptureCertificate.lean).
A coverage state carries the bits `rel, disp, rep` on a concern and `adm r, eff r, reg r`
on each route, plus `stands`; a concern is *live* when relevant, not disposed and not
represented; a route is *adequate* when all three route bits hold; `Covered` is
`live → ∃ r, adequate r` and `OpenTo` is `rel → stands`.  A *scenario* is an actual state
with a family of counterfactual states indexed by interventions.

**Definition 2.1 (Robust Openness at a state; manuscript 9.6).**

```
RobustOpenActual  :=  (actual.Covered ∧ actual.OpenTo)  ∧  ∀ j, (cf j).Covered ∧ (cf j).OpenTo
```
The actual branch is a separate conjunct, not a "do-nothing" intervention.

**Theorem 2.2 (Persistence certificate suffices; manuscript 9.7).**  Actual coverage
inside a protected route set `W`, actual standing, silent-branch coverage (`ClauseS`),
route persistence-or-replacement (`ClauseR`), and standing wherever applicable (`ClauseP`)
together give `RobustOpenActual`.  `Scenario.robustOpenActual_of_persistence`;
**registered** `openness.persistence-sufficient`; inhabited by
`Witness.persistence_inhabited`.  It is strictly stronger than necessary:
`Witness.persistence_not_necessary` exhibits `RobustOpen` with actual coverage and the
persistence clause false (**LEAN**).

**Theorem 2.3 (The split bill is Robust Openness; manuscript 9.5).**  Under actual
coverage in `W`,

```
ClauseS ∧ ClauseR⁺ W ∧ ClauseP   ↔   RobustOpen
```
`Scenario.certPlus_iff_robustOpen`; **registered** `openness.certplus-is-robust-openness`.
The certificate one might have hoped was cheaper is Robust Openness split on whether the
concern was live.

**Witness 2.4 (the actual branch is independent; manuscript 19.7).**  A scenario with
every counterfactual branch open and the actual branch lacking standing:
`RobustOpen ∧ ¬ActualOpen ∧ ¬RobustOpenActual`.
`Witness.counterfactual_open_not_actual`; **registered** `openness.actual-branch-witness`.

## 3. Legitimate Evolution

**Definition 3.1 (manuscript 10.1).**  An openness semantics assigns a scenario to each
accounted state and concern; `OpenAt sem O` is `RobustOpenActual` for every concern; a
*legitimate segment* is an Integrity evolution with `OpenAt` at every state,

```
LegitimateSegment sem O₀ O₁  :=  ⟨ ev : Evolution O₀ O₁,  ev.AllStates (OpenAt sem) ⟩
```
and `Legitimate sem O₀ O₁` is its inhabitation.  The semantics is state-indexed, which
is the canonicalization's one interface change.

**Theorem 3.2 (Composition; manuscript 10.2).**  `LegitimateSegment.trans` composes two
segments at a literally shared state; `Legitimate.trans` is the endpoint relation's
transitivity.  **registered** `legitimacy.segment-trans`, `legitimacy.endpoint-trans`;
inhabited by `Witness.composed`.

**Theorem 3.3 (Diachronic answerability; manuscript 10.3).**  For every legitimate segment,

```
Conservation O₀ O₁  ∧  OpenAt sem O₀  ∧  OpenAt sem O₁
```
`LegitimateSegment.answerable`; **registered** `legitimacy.answerable`.  Diachronic
answerability to the protected party decomposes exactly as conservation from Integrity
plus access and standing from Robust Openness; there is no characterization theorem
beyond the definition, and legitimacy certifies nothing about the correctness of the
commitments it carries.

**Witness 3.4 (endpoint openness is not enough; manuscript 19.6).**  An evolution whose
endpoints are open and whose middle state is not is not legitimate:
`Witness.endpoint_only_insufficient`; **registered** `legitimacy.endpoint-only-insufficient`.
Openness is required at every state along a segment, which is why segments carry their
intermediate states.

## 4. Structural liveness

Lean:
[`NormativeContinuity.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/aed09a697121e1d575473e3e7d87058ea85a49a3/lean/Workspace/Normativity/Contrib/NormativeContinuity.lean).
A matter `m` has, at stage `n`, a work set of ready reachable items and reachable waiting
cycles; `o_n(m) = 1[Work_n(m) ≠ ∅]` and `Ω_N(m) = Σ_{n<N} o_n(m)` is cumulative
opportunity.  Six structural trace hypotheses (fresh successors, prerequisite persistence
with named introduction, no future route roots, persistent satisfaction, only ready items
resolve, no silent rewiring into idleness) are the standing assumptions.

**Theorem 4.1 (Persistent Wait; manuscript 14.1).**  If `m` is structurally live forever
after some stage and `Ω_N(m)` is bounded, there is a prerequisite `d` and a stage `N₀`
such that `d` is a no-route wait for `m` at every `n ≥ N₀`.  `IssueTrace.persistent_wait`;
**LEAN**.

**Theorem 4.2 (Persistent Opportunity; manuscript 14.3).**  If `m` remains live forever
and is wait-responsive (every persistent no-route wait is eventually met), then
`Ω_N(m) → ∞`.  `persistent_opportunity`; **LEAN**.

**Theorem 4.3 (No Structural Abandonment; manuscript 14.4).**  Under wait responsiveness
and a non-starving attention rule (unbounded opportunity forces unbounded cumulative
attention), every matter either has no live docket descendant from some stage onward or
receives unbounded cumulative attention.  `no_structural_abandonment`; **LEAN**.  Nothing
here says attention produces a good answer.

## 5. Progress: the finite normative-error bound

Lean:
[`NormativeInductorComposition.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/aed09a697121e1d575473e3e7d87058ea85a49a3/lean/Workspace/Normativity/Contrib/NormativeInductorComposition.lean),
[`NormativeInductionInterface.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/aed09a697121e1d575473e3e7d87058ea85a49a3/lean/Workspace/Normativity/Contrib/NormativeInductionInterface.lean).

**Definition 5.1 (Normative error; manuscript 11.1).**  For an externally declared
evaluation of historical exposure (weights `μ_i ≥ 0`, `Σ μ_i = 1`), service occasions
`s`, an allocation `T_{is} ≥ 0` with row sums at most `μ_i`, anchored practical losses
`Λ_{is}(π_s) ∈ [0, D]` at the one actual response distribution `π_s`, and residual
`r_N := 1 − Σ_{i,s} T_{is}`,

```
E^norm_N  :=  Σ_{i,s} T_{is} Λ_{is}(π_s)  +  D · r_N
```
Unserved mass is charged the maximal loss.

**Contract 5.2 (Practical-response certificate; manuscript 12.1).**  For every assigned
pair, constants `M_{is}, ε_{is} ≥ 0` with `Λ_{is}(π_s) ≤ M_{is} δ_s + ε_{is}`, `δ_s` the
public defect at `s`.  **EXT** in general; two mechanized routes to it are in §6.

**Theorem 5.3 (Edge Progress bound; manuscript 13.1).**  With certificates on every
positive edge and the amplification bound `Σ_i T_{is} M_{is} ≤ Γ ν_s` for weights
`ν_s ≥ 0`, `Σ ν_s = 1`,

```
E^norm_N  ≤  Γ · Σ_s ν_s δ_s  +  Σ_{i,s} T_{is} ε_{is}  +  D · r_N
```
`edge_progress_bound`; **registered** `progress.edge-bound`.

**Theorem 5.4 (Quadratic form; manuscript 13.3).**  If enforcement intensities `λ_s`
and work `ρ_s` satisfy `λ_s δ_s² ≤ ρ_s`, with `ν_s = λ_s / Σ λ`,

```
E^norm_N  ≤  Γ · √( Σ_s ρ_s / Σ_s λ_s )  +  Σ T ε  +  D · r_N
```
`edge_progress_bound_quadratic`; **registered** `progress.edge-bound-quadratic`; all three
terms are positive in `edge_progress_witness`.  If `Γ` stays bounded and the three terms
vanish, `E^norm_N → 0`.

**Theorem 5.5 (Coercive uptake; manuscript 13.2).**  For any `ϕ : [0,D] → ℝ≥0` with
`ϕ̌(t) := inf_{x ≥ t} ϕ(x) > 0` for every `t > 0`, and `χ_N := Σ ν_s ϕ(δ_s)`,

```
Σ_s ν_s δ_s  ≤  Ψ_ϕ(χ_N)  :=  inf_{0 < t ≤ D} [ t + D χ_N / ϕ̌(t) ]
```
so the service-weighted mean defect vanishes whenever the uptake statistic does, and the
master bound is `E^norm_N ≤ Γ Ψ_ϕ(χ_N) + Σ T ε + D r_N`.  The quadratic case is
`ϕ(d) = d²`.  **paper-derived** in this general form (the manuscript mechanizes only the
quadratic specialization); the same inequality is the fixed-era actionability bound of §8
below.

**Theorem 5.6 (Progress on the accounted export; `ni.progress-bound`).**  For an
evaluation `E` of an accounted state and a practical-uptake certificate `C` at the
realized market,

```
E.progress market  ≤  E.modulus + E.error + E.D · E.residual
```
with `progress` the exposure-weighted anchored loss plus charged residual, `modulus` the
quadratic term, `error` the certificate slack, and `residual ∈ [0,1]` (`residual_bounds`).
`Evaluation.progress_bound`; **registered**; inhabited at a legitimate state by
`Witness.uptake`, `Witness.bound`.

**Witness 5.7 (headline loss is not edge loss).**  Two equally weighted services with
edge losses `0` and `1` average to `½`, below the headline loss `1`.
`edge_headline_separation`; **registered** `progress.headline-separation`.

## 6. The decision interface: how a certificate is earned

Lean:
[`NormativeInductor.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/aed09a697121e1d575473e3e7d87058ea85a49a3/lean/Workspace/Normativity/Contrib/NormativeInductor.lean),
[`PracticalCertificate.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/aed09a697121e1d575473e3e7d87058ea85a49a3/lean/Workspace/Normativity/Contrib/PracticalCertificate.lean),
[`GatedChoice.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/aed09a697121e1d575473e3e7d87058ea85a49a3/lean/Workspace/Normativity/Contrib/GatedChoice.lean).

**Theorem 6.1 (Approximate argmax transfer; manuscript 12.3).**  Finite menu `Q`;
displayed values `b`; target `v*` in a compact `V` of diameter at most `ζ` around it;
`δ := dist_∞(b, V)`; `π` an `η`-approximate maximizer of `b`.  Then

```
E_{q∼π}[ max_{q'} v*_{q'} − v*_q ]  ≤  2δ + 2ζ + η
```
`randomized_approximate_argmax_transfer` with `calibration_through_value_correspondence`;
**LEAN**.  With a Lipschitz loss this is a certificate with `M = 2L`.

**Theorem 6.2 (Adequate-set route).**  If the loss is at most `ε_ad` on an adequate set
`A` and the response puts mass at most `κ d + θ` outside `A`, then
`Λ ≤ (Dκ) d + (ε_ad + Dθ)`.  `adequate_set_route`; **LEAN**.  Any adapter that is sound at
the region point and ℓ¹-Lipschitz in the displayed state satisfies the mass condition
(`adapter_coupling`, `adapter_practicalCert`).

**Theorem 6.3 (Soft gate).**  Under `Region` (inadequate options priced at most `τ`),
`Within` (displayed within `d` of the region point) and a margin `W > 0` in either the
region point (`MarginMass`) or the displayed prices (`MarginDisplayed`), the soft gate
puts mass at most

```
( Σ_{q ∉ A} pref q ) / W  ·  d / δ
```
outside `A`, hence pays a practical certificate with `M = Dκ` for the corresponding `κ`.
`softGate_massOff_le_sharp`, `softGate_massOff_le_displayed`, `softGate_practicalCert`;
**LEAN**.  A hard gate has no Lipschitz constant (`Witness.hardGate_discontinuous`).

**Theorem 6.4 (Non-compensation).**  With a finite penalty `λ ≥ 0` on a bounded loss, any
stake above `λD` buys the violation (`scalar_bribery`), while a gate is invariant under
the stake (`gate_invariant`); **LEAN**.  A constraint that is a price is not a constraint.

**Counterexample 6.5 (the certificate is indispensable; manuscript 19.10).**  A displayed
price vector inside the compiled region, so `δ = 0`, whose argmax picks the worse policy
under the target values.  Zero defect says nothing about the response without Contract 5.2.
**FIX**.

## 7. The conditional Normative Inductor

**Theorem 7.1 (Traderization; imported).**  Add a computable trader to a trading firm
whose market satisfies the Logical-Induction no-exploitation criterion.  If the trader's
cumulative net worth is bounded below by a constant in every plausible assessment at
every date, the augmented firm still satisfies the criterion, and the market, if
computable, is a Logical Inductor relative to the same assessment.
`AssessmentFirm.trading_firm_dominance`, `no_efficient_trader_exploits`; **registered**
`li.assessment.firm-dominance`, `li.assessment.criterion`, `force.preservation`.  The
enforcement trader's conformance is the only place normative content enters the market:

```
Σ_j β_{t,j} g_j(P_t)²  ≤  ε_t + C^vol_t
```
`TraderizedEnforcement.weighted_square_le_slack_add_volume`; **registered**.  The
projection defect dominates the public sup-distance defect, which is what makes
`λ_s δ_s² ≤ ρ_s` of Theorem 5.4 a consequence of enforcement work (**LEAN**).

**Theorem 7.2 (Conditional Normative Inductor; manuscript 16.5).**  Suppose the
qualitative history through `N` is a legitimate segment; the evaluation and allocation
are as in Definition 5.1; every prefix used has a certified frame and decision/action
interface; the compiler produces a nonempty effective joint region at every occasion the
allocation uses; the projection enforcer supplies `(ρ_s, λ_s)` with `λ_s δ_s² ≤ ρ_s`;
scheduler and enforcer together satisfy the bounded-liability hypothesis of Theorem 7.1;
every assigned pair has a practical-response certificate; amplification holds; and the
augmented market is computable.  Then the augmented market is a Logical Inductor and

```
E^norm_N  ≤  Γ · √( Σ ρ_s / Σ λ_s )  +  Σ T ε  +  D · r_N
```
`Evaluation.conditional_normative_inductor` (bounded assessed liability ∧ computable market
∧ practical uptake ⟹ Logical Inductor ∧ the bound) and `deductive_normative_inductor`
(the deductive instance, with `λ d² ≤ ρ` *derived* from conformance).  **conditional**:
both are **LEAN** and deliberately unregistered, because no concrete realization inhabits
the semantic, compiler, liability, practical-response and computability hypotheses at
once.  The named remaining connectors are the compiler for a declared representable
class, the scheduler-to-liability connector, decision/action semantics, and
augmented-market computability ([Normative Inductor](Normative-Inductor)).

**Theorem 7.3 (Full spine; manuscript 17.1).**  Under the interface contracts (certified
frames, internal/settlement separation, grounded admission with authenticated semantics,
exhaustive semantic transfer with sound receipts), Robust Openness at every accounted
state, a declared evaluation and allocation, decision/action semantics, practical-response
certificates and a coercive uptake certificate with amplification:

1. *historical legitimacy* — every inherited anchored obligation is exactly accounted for
   as answered, validly closed, or faithfully carried live content, and every applicable
   declared concern remains actually and counterfactually open to the protected party
   throughout (Theorems 1.3, 3.3);
2. *effective normativity* — `E^norm_N ≤ Γ Ψ_ϕ(χ_N) + Σ T ε + D r_N` (Theorem 5.5), and
   in the quadratic realization Theorem 5.4.

The two conclusions are logically independent: legitimacy does not give low error, low
error does not give legitimacy.  The Logical-Induction realization is one route to the
uptake side, not part of the spine.

## 8. Fixed-era service and affordability (Layer I)

Every result in this section is **paper-derived** with exact fixtures, from the
[normative-affordability round](https://github.com/A-M-Berns/alignment-workspace/tree/aed09a697121e1d575473e3e7d87058ea85a49a3/projects/normativity/legitimacy/rounds/2026-08-31-normative-affordability),
and none is in Lean; the status ledger says so explicitly.  They are the fixed-era
predecessors of §5: one reason, one enforcement account, obligations weighted by a
service measure `ν` or an obligation measure `μ`.

**Theorem 8.1 (Actionability, F1;
[`FIXED_ERA_THEOREM.md`](https://github.com/A-M-Berns/alignment-workspace/blob/aed09a697121e1d575473e3e7d87058ea85a49a3/projects/normativity/legitimacy/rounds/2026-08-31-normative-affordability/FIXED_ERA_THEOREM.md) §1).**
With work `Work_N = Σ a_t ϕ(d_t)` and intensity `A_N = Σ a_t`:
`Work_N / A_N → 0` and `ϕ̌(ε) > 0` for all `ε > 0` give `E_ν[d] → 0`, the second condition
being necessary; quantitatively `E_ν[d] ≤ inf_ε [ε + D (Work_N/A_N) / ϕ̌(ε)]`, and for
convex strictly increasing `ϕ` with `ϕ(0) = 0`, `E_ν[d] ≤ ϕ⁻¹(Work_N/A_N)`.

**Theorem 8.2 (Service-weighted Progress, F2; §2).**  For every world live at `N`,

```
E_ν[d]  ≤  ‖s⁺_r(ω)‖_{L²(ν)}  +  √( (U + B_tot) / A^r_N )
```
with `U` the MarketMaker cap and `B_tot` the total liability floor.  The earlier claim that
per-reason uptake is free from the Logical-Induction criterion is **withdrawn**; uptake is
the cap `V^r_N(ω) ≤ U`.

**Theorem 8.3 (Deferred service transfer, T3;
[`SERVICE_TRANSFER.md`](https://github.com/A-M-Berns/alignment-workspace/blob/aed09a697121e1d575473e3e7d87058ea85a49a3/projects/normativity/legitimacy/rounds/2026-08-31-normative-affordability/SERVICE_TRANSFER.md)).**
Given an adapted transport plan `T_N` with obligation marginal, feasibility against the
service intensities, cap `W_N ≤ K C_N`, residual `R_N / C_N → 0`, and semantic stability
`d_t ≤ L d_s + ε(t,s)` on the plan's support,

```
E_μ[d]  ≤  L K · E_ν[d]  +  ε̄_N(T)  +  D · R_N / C_N
```
Contiguity `μ ◁ ν` is necessary and sufficient for the qualitative transfer on triangular
arrays (T1 sufficiency is Le Cam's, inherited), and the two-surface fair-rotation
countermodel shows service-weighted defect `0` with obligation-weighted defect `½`, so a
transfer needs an interface: `c_n ≥ c_* > 0` on every service date gives
`μ_N ≤ ν_N / c_*`.

**Theorem 8.4 (Bounded delay, BD1/BD2/D4;
[`BOUNDED_DELAY_AFFORDABILITY.md`](https://github.com/A-M-Berns/alignment-workspace/blob/aed09a697121e1d575473e3e7d87058ea85a49a3/projects/normativity/legitimacy/rounds/2026-08-31-normative-affordability/BOUNDED_DELAY_AFFORDABILITY.md)).**
A plan serving every claim within delay `H` exists iff `Σ_{[u,v]} c ≤ Σ_{[u,v+H]} a` for
every interval (a Gale–Hoffman condition; see [Prior Art](Prior-Art)); FIFO is optimal and
complete; on the linear branch the cheapest cost is
`Cost_H(c) = Σ_t c_t · min{ w_s : s ∈ [t, t+H] }`.  The manuscript's
predictable-window scheduler (16.4) is the mechanized form of this rule: schedule each
arrival at its window's cheapest date; affordability `Σ c_t w^min_t ≤ B` then gives a
plan within the known windows, within budget, serving every claim in full.

**Theorem 8.5 (Sharp persistence, S1–S3;
[`SHARP_PERSISTENCE.md`](https://github.com/A-M-Berns/alignment-workspace/blob/aed09a697121e1d575473e3e7d87058ea85a49a3/projects/normativity/legitimacy/rounds/2026-08-31-normative-affordability/SHARP_PERSISTENCE.md)).**
For increasing star-shaped liability functions `L_t` with `L_t(0) = 0`, a schedule with
`Σ a_t = ∞` and `Σ L_t(a_t) ≤ B` exists iff `liminf_t L_t(1) = 0`; the maximal affordable
intensity through `N` is `max_t L_t⁻¹(B)`; and for the quadratic-with-volume liability
`¼ min(s², s√m) ≤ L(1) ≤ min(s², s√m)`.  Under exogenous star-shaped liabilities, finite
claims with infinite total mass, fungible service and unlimited deferral, a persistent
affordable schedule exists iff an affordable plan discharging every claim exists, both iff
`liminf L_s(1) = 0`
([`EVENTUAL_VS_UNIFORM_SERVICE.md`](https://github.com/A-M-Berns/alignment-workspace/blob/aed09a697121e1d575473e3e7d87058ea85a49a3/projects/normativity/legitimacy/rounds/2026-08-31-normative-affordability/EVENTUAL_VS_UNIFORM_SERVICE.md));
uniform timeliness is strictly stronger.

**Theorem 8.6 (Sharp Timely Service — the Layer I endpoint;
[`SHARP_TIMELY_SERVICE.md`](https://github.com/A-M-Berns/alignment-workspace/blob/aed09a697121e1d575473e3e7d87058ea85a49a3/projects/normativity/legitimacy/rounds/2026-08-31-normative-affordability/SHARP_TIMELY_SERVICE.md)).**
Under (S) an adapted plan with `A^r_N → ∞`, parsimony `K_r`, and vanishing residual
density; (L) `a^r_t ≤ 4 m_t / (D^r_t)²` and `Σ ¼ a^r_t (D^r_t)² ≤ B_r`; (M) `U_r = U + B_tot`;
(N) nesting of the enforcement supports; (T) semantic stability
`d^r_t ≤ L_r d^r_s + ε_r(t,s)`:

```
E_{μ^r_N}[d^r]  ≤  L_r K_r (2√B_r + √U_r) / √A^r_N  +  ε̄^r_N(T)  +  D̄_r R^r_N / C^r_N
```
Corollaries: the limsup is at most the limsup of the stability slack; it is at most the
modulus `ω_r(H)` under uniform delay; it vanishes under exact preservation; and a norm that
excludes every live world by a margin `σ > 0` on the linear branch cannot be persistently
affordably enforced, since `σ² A_N ≤ 4B`.  The ledger warns this is *not* proved beyond
the round's own mathematics.

**Theorem 8.7 (Liability accounting;
[`REASONWISE_ACCOUNTING.md`](https://github.com/A-M-Berns/alignment-workspace/blob/aed09a697121e1d575473e3e7d87058ea85a49a3/projects/normativity/legitimacy/rounds/2026-08-31-normative-affordability/REASONWISE_ACCOUNTING.md)).**
The account identity `V_N(w) = Σ w_t (d_t − s_t)` (signed misfit); common-mixture
affordability `E_N(ω) ≥ −U(1−θ)/θ`; per-row floors `Σ B_j ≤ B_tot` give the subset
ceiling `U + B_tot` while aggregate safety alone does not; local capacity is not lifetime
safety; conservative underwriting is strictly and unboundedly smaller than signed-account
affordability; a scalar slack is not sufficient state.

The open items of this layer are the manuscript's frontier: adaptive affordability for
closed-loop or adversarial dockets, quantitative semantic transport (deriving `M, ε` from
qualitative faithfulness), joint practical-response compatibility at one occasion,
endogenous liveness, and many-parent semantic aggregation.  All **OPEN**.

## 9. Legitimate deference: activated value

Lean:
[`ActivatedValue.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/aed09a697121e1d575473e3e7d87058ea85a49a3/lean/Workspace/Deference/Contrib/ActivatedValue.lean),
[`PartialActivatedValue.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/aed09a697121e1d575473e3e7d87058ea85a49a3/lean/Workspace/Deference/Contrib/PartialActivatedValue.lean),
[`ReasonCoverage.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/aed09a697121e1d575473e3e7d87058ea85a49a3/lean/Workspace/Deference/Contrib/ReasonCoverage.lean),
[`ReasonMediatedAuthorship.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/aed09a697121e1d575473e3e7d87058ea85a49a3/lean/Workspace/Deference/Contrib/ReasonMediatedAuthorship.lean);
statement of record
[`LEGITIMATE_DEFERENCE.md`](https://github.com/A-M-Berns/alignment-workspace/blob/aed09a697121e1d575473e3e7d87058ea85a49a3/projects/deference/rounds/2026-09-08-legitimate-deference-consolidation/LEGITIMATE_DEFERENCE.md).
Nothing in this section is registered.  The objects: a credence `π` over worlds, an
activation indicator `c` (the account's fates are exactly `{answered}`), a *partial*
future evaluation `Ṽ` defined where `c` holds, and a followed strategy `α`.  Activated
regret `R_U` is regret on the activated securities `c · Ṽ`; authoritative regret `R_auth`
is regret conditional on activation; `voidMass` is the mass where `c` fails.

**Theorem 9.1 (Identity).**  `0 < mass π c` gives `R_U = mass π c · R_auth`, for every
completion of `Ṽ`.  `regretU_eq_mass_mul_regretAuth`; **LEAN**.

**Theorem 9.2 (Conditional authoritative regret — the primary conclusion).**  With
`Σ π = 1`, `voidMass π c ≤ η < 1`, `0 ≤ ε` and `R_U ≤ ε`:

```
1 − η  ≤  mass π c        and        R_auth  ≤  ε / (1 − η)
```
`regretAuth_le_div`; **LEAN**.  The sign hypothesis `0 ≤ ε` is load-bearing.  Asymptotic
form: `R_U ≲ 0` and `η_n → 0` give `R_auth ≲ 0` (`regretAuth_asymptotic`).  Regret is
against the best *fixed* candidate and is not assumed nonnegative.

**Theorem 9.3 (Completion is two-sided, and the one-sided interval is withdrawn).**  For
`π ≥ 0`, `α` a probability vector at every world, values in a band of width `D`,

```
| R_{V̄} − R_U |  ≤  D · voidMass π c
```
for every completion `V̄`.  `regretV_sub_regretU_abs_le`; **LEAN**; both constants sharp
(`Sharp.transfer_sharp`, `SharpLower.attained`).  The earlier statement
`R_{V̄} ∈ [R_U, R_U + Dη]` was **false**: a world-dependent followed strategy uses the void
branch to beat every fixed candidate, and `SharpLower.attained` exhibits
`R_U = 0`, `R_{V̄} = −½ = R_U − Dη`.  The upper one-sided corollary stands
(`availability_transfer_completion`).  Completions are not authoritative.

**Theorem 9.4 (Reason coverage).**  Representation faithfulness on the protected scope
(`Rep ⇒ InTrace`) and the barrier (`c = 1 ⇒ no live protected concern`) give certified
coverage: activation implies every active protected concern is in the reason trace
(`covered_of_barrier`); an omitted active protected concern forces `c = 0`
(`void_of_omitted`); under coverage the mass of coverage failure is at most the void mass
(`covFail_mass_le`).  Robust Openness supplies route *availability* for a live concern
(`route_of_live`) and nothing about its exercise.  **LEAN**.

**Theorem 9.5 (Reason mediation and channel blindness).**  A value `V` on outcomes is
*reason-mediated* at fixed principal policy `z` iff it factors through the declared reason
view: `V ∘ β(·,z) = F_z ∘ R ∘ β(·,z)` (`reasonMediated_iff_factor`).  If `R` is blind to a
channel and `V` is reason-mediated then `V` is blind to it (`blind_of_mediated`); selection
blindness is blindness to the selection-induced pair class (`selectionBlind_iff_blind`).
Witnesses: an earlier disposition write defeats the session-local form
(`Witness.earlyWrite`); selection leaks through other session inputs with no literal
preview (`Witness.leak`).  **LEAN**.  Authorship is *issuance-rooted*: the same predicate
instantiated on the advisor's whole continuation and a reason trace.

**Theorem 9.6 (The characterization, A1–A4).**  Sound activation (the seven clauses of the
record: answer receipt, authentic binding, principal-exclusive endpoint, occurrence-local
Integrity trace, scoped Robust Openness, issuance-rooted reason-mediated authorship, the
reason-coverage barrier), the value-domain condition (**PAPER** scope), ordinary
Logical-Induction Value on the activated securities giving `R_U ≤ ε` (**PAPER**,
`InheritedAlgebra.value_asymptotic`), and availability `η_n < 1` (**OPEN**, item 87)
together give Theorems 9.2 and 9.3.  The activation semantics is **EXT**.

## 10. Corrigibility

Lean:
[`SelectedTrustNonPreemption.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/aed09a697121e1d575473e3e7d87058ea85a49a3/lean/Workspace/Deference/Contrib/SelectedTrustNonPreemption.lean);
documents
[`ARCHITECTURE.md`](https://github.com/A-M-Berns/alignment-workspace/blob/aed09a697121e1d575473e3e7d87058ea85a49a3/projects/deference/rounds/2026-09-06-corrigibility-architecture/ARCHITECTURE.md),
[`INCENTIVE_CORRIGIBILITY.md`](https://github.com/A-M-Berns/alignment-workspace/blob/aed09a697121e1d575473e3e7d87058ea85a49a3/projects/deference/rounds/2026-09-06-incentive-nonpreemption/INCENTIVE_CORRIGIBILITY.md),
[`NORMATIVE_CHOICE_THEOREM.md`](https://github.com/A-M-Berns/alignment-workspace/blob/aed09a697121e1d575473e3e7d87058ea85a49a3/projects/deference/rounds/2026-09-06-decision-theory-bill/NORMATIVE_CHOICE_THEOREM.md).
Nothing registered.

**Theorem 10.1 (No Laundered Authority Loss).**  Under the bridges B1 (efficacy
faithfulness: the `eff` bit tracks actual affordance), B2 (registration faithfulness: the
docket enters coverage through `rep`) and B3 (disposition places the load on a
successor), at any state where the correction affordance is lost exactly one of the
following holds: *amended* (relevance false, with a closure receipt); *disposed*;
*registered debt* (a live restoration occurrence, conserved by Theorem 1.3); or *not open*
(the state fails `OpenAt`).  The fourth combination — loss, open, no amendment,
disposition or docket entry — is unreachable, and dropping B2 readmits it.  **FIX**
(exhaustive over coverage states and docket) and **paper-derived** from Theorems 2.1 and
3.3; the Lean form is item 83.  It is a corollary of per-state Robust Openness plus
conservation, not a new pillar.

**Theorem 10.2 (Level I identity and non-preemption).**  For a selected-trust index `σ`
and the principal's choice `J`,

```
valuation σ − valuation J  =  selectedGap + principalRegret
```
(`valuation_sub_eq`), so `selectedGap ≤ ε` and `principalRegret ≤ r` give gain at most
`ε + r` (`nonpreemption`); the weakest form against `max(Y, 0)` is the conclusion itself
when the principal never regrets (`nonpreemption_plus`); the delegation bridge is the
pointwise instance (`delegation_bridge_of_nonpreemption`).  **LEAN**.

**Theorem 10.3 (Principal-side calibration).**  Cellwise `|w − b| ≤ δ`, `|W − w| ≤ ζ` and an
`η`-approximate argmax give `principalRegret ≤ 2δ + 2ζ + η`
(`principalRegret_le_of_calibration`), hence a choice gap of at most
`ε_ST + 2δ + 2ζ + η` (`nonpreemption_of_calibration`, nonvacuous by `Witness.nonvacuous`);
**LEAN**, through Theorem 6.1.  If the sealed target reads the quote, `ζ ≥ ½` and the
bound is vacuous (**FIX**): a sealed arm is needed.

**Theorem 10.4 (Level II, mediated delegation).**  Over non-foreclosing conducts the
admissible-preemption deficit splits exactly as accounting deficit plus selected gap plus
principal regret on the override region, giving

```
Δ^{admissible preemption}  ≤  2B · eps_pred + ε_ST + r_P,     r_P ≤ 2δ + 2ζ + η
```
**FIX** (exhaustive over four episodes); not Lean.

**Theorem 10.5 (Violation decomposition and the foreclosure premium).**
`Δ^phys ≤ Δ^C + Φ_C` with `Φ_C = sup_π (V(π) − V(R_C π))₊` (`violation_decomposition`);
selected repair trust gives `Φ_C ≤ ε_C` (`premium_of_selected_repair_trust`) but is
strictly stronger than its conclusion (`ct_strictly_stronger`), so the higher levels of
the hierarchy are relabelings and are not reached.  **LEAN**.

**Theorem 10.6 (Dynamic admissibility).**  When an admissible act changes the next
admissible set, a myopic gated learner is legitimate but loses `2H − 3` to the investing
policy over horizon `H`; an untyped gate is hacked; a typed gate is safe and incompetent
(**FIX**).  The learner that closes this is [Continuation BRIA](Continuation-BRIA), whose
own results are on that page: duration-weighted bounded inductive rationality over block
continuations, the sharp rejection bound `ℓ_K < w_K − A_i(K)`, existence exactly on
non-dominant block schedules, the settlement-timing impossibility, and the exact
decomposition `Regret = LEARN + SLACK + SHIFT` with `LEARN` controlled and the two
bridges open (item 86).

## 11. The counterexamples that fix the shape

Each of these is exact and is why the corresponding definition has the form it has.

| witness | forces |
|---|---|
| one semantic value cannot carry two debts (`a ⊔ a = a`) | anchored historical identities (Witness 1.5) |
| an append-only record can carry a false "answered" label | adequacy certificates separate from record integrity |
| a balanced transfer equation can drop a criticism-relevant distinction | semantic authentication and order-reflecting faithfulness |
| a settlement item about `X` cannot close an obligation about `Y` | the stored closure judgment, separate from settlement membership |
| recomputing closure under current rules rewrites historical fate | stored closure certificates; reconsideration is prospective |
| open → blocked → open | per-state openness along segments (Witness 3.4) |
| every counterfactual branch open, the actual one not | the actual branch as its own conjunct (Witness 2.4) |
| an adequate route vanishes while another replaces it | persistence is a certificate, not the definition (Theorem 2.2) |
| two nonempty regions with empty intersection | one joint compiled region, never per-obligation projection |
| zero defect, worse policy ranked first | the practical-response certificate as an independent bridge (6.5) |
| a world-dependent strategy on the void branch | the two-sided completion theorem (Theorem 9.3) |
| a sparse tester that always reverts, on a revocable amendment | continuation claims rather than the one-step criterion ([Continuation BRIA](Continuation-BRIA)) |

## 12. What is external, what is open

**External by design** (enters only through a typed contract): concern scope;
the agent–environment boundary and counterfactual coupling; truth of settlement sources;
substantive semantics of answer adequacy and closure; response readout and anchored loss;
evaluation weights; any final moral theory or utility function.  The manuscript's
interface table lists each supplier's obligation.

**Open** (filed, not settled): the fixed-era frontier of §8; the connectors of Theorem
7.2; the semilattice conservation theorem as one Lean declaration (§1); the Lean form of
No Laundered Authority Loss (item 83); the operative-value-security bridge (item 84);
margin realization (item 85); promise recognizability and joinability for continuation
BRIA (item 86); the realization bill for legitimate deference (item 87); affordability
from the traderization perspective (item 88).  The open queue itself lives in
[`PRIORITIES.md`](https://github.com/A-M-Berns/alignment-workspace/blob/aed09a697121e1d575473e3e7d87058ea85a49a3/PRIORITIES.md);
this page names items, it does not maintain them.
