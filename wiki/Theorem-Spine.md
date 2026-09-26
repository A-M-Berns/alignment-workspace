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
| **registered** | a Lean declaration listed in a claims registry ([normativity](https://github.com/A-M-Berns/alignment-workspace/blob/aed09a697121e1d575473e3e7d87058ea85a49a3/projects/normativity/CLAIMS.md), [deference](https://github.com/A-M-Berns/alignment-workspace/blob/f03c8072fc840fb900f6be44a619375686dc6b26/projects/deference/CLAIMS.md)) at class `lean-proved`; the registry row, not this page, is the record |
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

## 3. The open Integrity evolution, and legitimacy

**Definition 3.1 (manuscript 10.1).**  An openness semantics assigns a scenario to each
accounted state and concern; `OpenAt sem O` is `RobustOpenActual` for every concern; an
*open Integrity segment* is an Integrity evolution with `OpenAt` at every state,

```
OpenIntegritySegment sem O₀ O₁  :=  ⟨ ev : Evolution O₀ O₁,  ev.AllStates (OpenAt sem) ⟩
```
and `OpenIntegrity sem O₀ O₁` is its inhabitation.  The semantics is state-indexed, which
is the canonicalization's one interface change.  This conjunction — the Integrity
conjunct of internal legitimacy with the Robust Openness conjunct of external legitimacy
— is the record half of legitimacy and the object the activated-value stack of §9
consumes.

**Theorem 3.2 (Composition; manuscript 10.2).**  `OpenIntegritySegment.trans` composes
two segments at a literally shared state; `OpenIntegrity.trans` is the endpoint
relation's transitivity.  **registered** `open-integrity.segment-trans`,
`open-integrity.endpoint-trans`; inhabited by `Witness.composed`.

**Theorem 3.3 (Diachronic answerability; manuscript 10.3).**  For every open Integrity
segment,

```
Conservation O₀ O₁  ∧  OpenAt sem O₀  ∧  OpenAt sem O₁
```
`OpenIntegritySegment.answerable`; **registered** `open-integrity.answerable`.
Diachronic answerability to the protected party decomposes exactly as conservation from
Integrity plus access and standing from Robust Openness; there is no characterization
theorem beyond the definition, and nothing here certifies the correctness of the
commitments the record carries.

**Witness 3.4 (endpoint openness is not enough; manuscript 19.6).**  An evolution whose
endpoints are open and whose middle state is not is not an open Integrity evolution:
`Witness.endpoint_only_insufficient`; **registered** `openness.endpoint-only-insufficient`.
Openness is required at every state along a segment, which is why segments carry their
intermediate states.

**Definition 3.5 (Legitimacy).**  Over a declared interaction frame `(β, x, R, V, D)` —
the continuation frame, the declared-input view, the reason trace, the payload and the
audited class — a segment of the principal's trajectory is **legitimate** iff it is
*internally* legitimate — an Integrity evolution of the record, and authorship
`ReasonMediated β R V D z` at every exterior (the payload factors through the reason
trace) — and *externally* legitimate — Robust Openness at every state, and transparency
`Realizes β x R κ D` (the reason channel realizes its declared reference `κ` on the
declared inputs).  **LEAN** `Legitimacy.Segment`, `Legitimacy.Internal`,
`Legitimacy.External`.  Legitimacy composes at a shared state (`Segment.trans`) and
projects to an open Integrity segment (`Segment.toOpenIntegrity`), so Theorem 3.3 holds
of it (`Segment.answerable`).  It certifies nothing about the starting state.  This is
the *frame-level* form; the general form is time-indexed — authorship and transparency
required only at the steps inside the segment, on a reason-trace interface with the
record's own clock — and the frame-level form is its special case over the trivial
interface (**LEAN** `GateIsLegitimacy.Segment`, `ofFrameLevel`; the gate on future
evaluations is the existence of a time-indexed segment, `Counted`).

**Theorem 3.6 (The payload factors through the declared inputs).**  Under legitimacy,
two audited continuations with the same declared inputs at an exterior yield the same
payload: `V = G ∘ x`, internal (authorship) composed with external (transparency).
**LEAN** `Segment.payload_of_view`; inhabited by `Witness.segment`.  In the time-indexed
form the same conclusion takes the segment's starting prefix and the principal's own
earlier entries as hypotheses (`GateIsLegitimacy.Segment.payload_of_view`).  The renaming of the
registered spine to this vocabulary is recorded with its old-to-new map in the normativity
claims registry.

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
reason-coverage barrier — the occurrence-local reading of legitimacy's four conjuncts,
with authentic binding under Integrity, the trace and openness the record half, authorship
the internal channel conjunct and channel blindness a face of transparency), the
value-domain condition (**PAPER** scope), ordinary
Logical-Induction Value on the activated securities giving `R_U ≤ ε` (**PAPER**,
`InheritedAlgebra.value_asymptotic`), and availability `η_n < 1` (**OPEN**, item 87)
together give Theorems 9.2 and 9.3.  The activation semantics is **EXT**.

**Theorem 9.7 (Reason mediation by re-execution — registered).**  In the evaluation
ecosystem — a `Protocol` read off an authenticated event log, with Integrity propagation
proved a function of the log (`propagate_segment_eq`, `complete_accounting_eq`) and
activation a reading of it (`activated_iff`) — let the mandate carry a principal program
`π_P : ℛ → 𝒱` in a total first-order language over the reason trace and let a valid
answer re-execute it on the commit's strict prefix.  Then for any frame `β : Q → Z → Log`,
any audited class `D` of activated continuations sharing the mandate, and any policy `z`,

```
ReasonMediated β (traceAtCommit · o) (payload · o) D z ,      factor map  eval π_P
```
(`reasonMediated_of_reexecution`, **registered** `authorship.mediation-by-reexecution`;
inhabited by `Instance.mediation_witness`, two continuations with equal traces and
different logs).  Blindness transfers (`blind_payload_of_reexecution`) and exclusive
binding follows from a party-bound warrant registry (`exclusiveBind_of_registry`).  A
commit whose vector is not the program's output is void, not a foreign receipt
(`Instance.miscomputation_void`); a coincident computation yields the same log
(`Instance.logs_equal`), so computational integrity is not a hypothesis.  Register
programs are a separate syntactic class (`Programs.susceptible_not_trace`).  The
representation-faithfulness bridge holds for every log and scope
(`rep_faithful`, **LEAN**).  What remains of item 87 after this: reason-supply liveness
(the bounded-delay affordability criterion for the concern stream), selection-induced
sealing (partial; the advisor's view leaks the selection back, so re-execution does not
transfer to the advisor), and availability (`η_n → 0`; the ecosystem's Laplace price
tracks the empirical void frequency within `3/(n+2)`, `laplace_eta_sub_freq_abs_le`).
Lean:
[`EvaluationEcosystem.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/f03c8072fc840fb900f6be44a619375686dc6b26/lean/Workspace/Deference/Contrib/EvaluationEcosystem.lean);
records
[`CLAUSE_LEDGER.md`](https://github.com/A-M-Berns/alignment-workspace/blob/f03c8072fc840fb900f6be44a619375686dc6b26/projects/deference/rounds/2026-09-10-committed-principal-program/CLAUSE_LEDGER.md)
and
[`PRINCIPAL_PROGRAM.md`](https://github.com/A-M-Berns/alignment-workspace/blob/f03c8072fc840fb900f6be44a619375686dc6b26/projects/deference/rounds/2026-09-10-committed-principal-program/PRINCIPAL_PROGRAM.md).

## 10. Corrigibility

Lean:
[`Corrigibilization.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/a192d3f76a3887fe87fe6db52f2e9d8d16037760/lean/Workspace/Deference/Contrib/Corrigibilization.lean),
[`LICorrigibility.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/a192d3f76a3887fe87fe6db52f2e9d8d16037760/lean/Workspace/Deference/Contrib/LICorrigibility.lean),
[`LICorrigibilityCertificate.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/a192d3f76a3887fe87fe6db52f2e9d8d16037760/lean/Workspace/Deference/Contrib/LICorrigibilityCertificate.lean),
[`MediatedRepairDominance.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/f03c8072fc840fb900f6be44a619375686dc6b26/lean/Workspace/Deference/Contrib/MediatedRepairDominance.lean),
[`SelectedTrustNonPreemption.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/aed09a697121e1d575473e3e7d87058ea85a49a3/lean/Workspace/Deference/Contrib/SelectedTrustNonPreemption.lean);
documents
[`CORRIGIBILIZATION.md`](https://github.com/A-M-Berns/alignment-workspace/blob/f03c8072fc840fb900f6be44a619375686dc6b26/projects/deference/rounds/2026-09-09-mediated-repair-dominance/CORRIGIBILIZATION.md),
[`THIRD_PASS.md`](https://github.com/A-M-Berns/alignment-workspace/blob/f03c8072fc840fb900f6be44a619375686dc6b26/projects/deference/rounds/2026-09-09-mediated-repair-dominance/THIRD_PASS.md),
[`THEOREM.md`](https://github.com/A-M-Berns/alignment-workspace/blob/a192d3f76a3887fe87fe6db52f2e9d8d16037760/projects/deference/rounds/2026-09-15-li-corrigibility/THEOREM.md) and [`LANDING.md`](https://github.com/A-M-Berns/alignment-workspace/blob/a192d3f76a3887fe87fe6db52f2e9d8d16037760/projects/deference/rounds/2026-09-15-li-corrigibility/LANDING.md) of the
li-corrigibility round,
[`ARCHITECTURE.md`](https://github.com/A-M-Berns/alignment-workspace/blob/aed09a697121e1d575473e3e7d87058ea85a49a3/projects/deference/rounds/2026-09-06-corrigibility-architecture/ARCHITECTURE.md),
[`INCENTIVE_CORRIGIBILITY.md`](https://github.com/A-M-Berns/alignment-workspace/blob/aed09a697121e1d575473e3e7d87058ea85a49a3/projects/deference/rounds/2026-09-06-incentive-nonpreemption/INCENTIVE_CORRIGIBILITY.md).
Nothing in this section is registered.  The setting: a finite two-stage interaction
(agent move, principal response, exterior move); one continuation space `Π(h)`, no
primitive class; protected concerns `r ∈ Γ` with immediate response semantics `φ_r`;
**response authority** `K_r(s_A)` — after the agent's move some principal response
realizes `φ_r` now; an **agent-caused loss** — `K_r` fails after the actual move and
would hold after the idle move; the **authorization interface** — approve/decline
decision responses with decline preservation; a loss at step `t` is **authorized**
(event-linked) iff the agent's move at `t` is the gated release of an effect `e` whose
latch the principal's approval of `e`'s proposal set at an earlier step, and the decline
alternative at that step has no agent-caused loss of `r` at step `t` — the earlier
"every later loss" clause is refuted for repeated effects (`ShopRepair`, **FIX**);
`Corrigible_h(π, ρ)` iff every agent-caused protected loss under rule `ρ` is authorized.  The forcing-type comparison is **FIX** (M, N):
global forcing is false before any bypass, continuation-relative forcing is
anticipatory, response authority is present-tense.

**Theorem 10.1 (Corrigibilization soundness, C1 / T1).**  `𝔠` rewrites every raw
release of a declared effect into a proposal followed by a gated release and passes
everything else through.  Under effect completeness (EF) — in the abstract interaction,
task moves never remove response authority — with mediation soundness (MS), decline
preservation (DP) and execution faithfulness (EX) holding by construction of the
response stage, `∀π ∈ Π(h) ∀ρ. Corrigible_h(𝔠π, ρ)` for every rule `ρ` that does not
correct at the authorizing step, with event-linked authorization.  **LEAN** at the
trajectory level (`Corrigibilization.corrigible_corrPolicy`; inhabited by
`Witness.corrigible_instance`, with `Witness.raw_cut_loses` the raw loss it authorizes);
the step lemma `loss_conditional_on_decision` and `corr_no_raw` are the 2026-09-09
**LEAN**; **FIX** A, E, `ShopRepair`.  Necessity of EF: **FIX** F (`𝔠π_F = π_F`, an
undeclared move's loss is unauthorized).  EF is **EXT**.

**Theorem 10.2 (Closure, C2).**  `corr (corr ms) = corr ms` (`corr_idem`),
`corr ms = ms ↔ NoRaw ms` (`corr_fix_iff`), and on policies
`corrPolicy (corrPolicy π) = corrPolicy π` (`corrPolicy_idem`); **LEAN**.  Hence
`𝔠π = π ⟹ Corrigible(π)` under 10.1's hypotheses; the converse fails without effect
soundness (**FIX** B, distance `1/4`).  Corrigibility is not `Fix(𝔠)`.

**Theorem 10.3 (Approval reproduces the raw policy, C3).**  The raw residual frame maps
into `𝔠π`'s by a Cartesian-frame morphism with agent component "approve" and identity
exterior; forcing is monotone along it (`ensures_mono`, `approvalMorphism`, **LEAN**).
The morphism's failure on the protected projection is the structural discrepancy `δ`;
with an `L`-stable protected value, `(w_raw − w_approve)₊ ≤ L·δ`
(`mediationGap_le_of_lipschitz`) and `W(π) ≤ W(𝔠π; ρ) + L·E[δ] + E[ρ]`
(`option_dominance_of_approx_reproduction`), **LEAN**.  A generic constraint's repair
cannot keep the effect as an approve branch (**FIX** Q: `7/4 < 9/4 < 5/2`).

**Theorem 10.4 (Corrigibilization dominance, C5–C6).**  With one activation event `c`
common to `{π, 𝔠π}`, `|w_raw − w_approve| ≤ L·δ` and `w_approve − w_act ≤ ρ` on the
activated worlds,

```
E[c·w_raw] − E[c·w_act]  ≤  L·E[c·δ] + E[c·ρ]
```
(`security_score_bypass_le_sharp`, **LEAN**; mediation cost on unsettled worlds is not
charged); with prices within `ε` of the securities' expectations the score gap is at
most that plus `ε` (`security_score_bypass_le_of_prices` for the unsharpened form);
over a finite family the largest positive gap is at most the largest bound
(`uniform_bypass_le`, **LEAN**; **FIX**: five raw continuations of A, `Φ_corr = 1/2 ≤ 1`).
So `Φ_corr,n(h) := sup_{π∈Π(h)} [S_n(π) − S_n(𝔠π)]₊ ≤ sup_π (L·E[c·δ_π] + E[c·ρ_π] + ε_n(π))`,
and under uniform bounds `≤ L·δ̄ + ρ̄ + ε̄ → 0`.  The chooser scoring by `P_n(U_q)` loses at
most `ε + 2ε_cal` by its choice (`operative_choice_loss`, **LEAN**).  The sealed common
comparison is **EXT** (item 89): under same-branch evaluation the raw candidate can end
the evaluation (**FIX** E2, `η_raw = 1`, `Witness.totalVoid`); a hindsight evaluator is
sealed only under a declared physical factorization an undeclared move violates (E1-sever);
sequenced settlement seals the comparison for every `π` at the price of an ex-ante
judgment (`ShopSeq`, **FIX**).  Price calibration is the Value hypothesis of §9
(**PAPER**).

**Theorem 10.4a (Directional activation mismatch, T2).**  With per-option activation
events `c_raw, c_corr` on one world space, `both = c_raw ∧ c_corr`,
`M = c_raw ∧ ¬c_corr`:
```
U_raw − U_corr  =  both·(w_raw − w_act) + M·w_raw − (¬c_raw ∧ c_corr)·w_act
E[U_raw] − E[U_corr]  ≤  L·E[both·δ] + E[both·ρ] + D·E[M]
```
under the reproduction certificate and decline regret on `both` and values in `[0, D]`
(`mismatch_identity`, `mismatch_bound_exact`, `mismatch_bound`,
`security_bypass_le_mismatch`, **LEAN**).  `D` is attained (`Witness.attained`); the
marginal-rate form `D·(E[c_raw] − E[c_corr])` is false (`Witness.marginal_refuted`); the
reverse term is never charged (`Witness.reverse_free`); `M ≡ 0` recovers Theorem 10.4
(`mismatch_common`).  **FIX**: attained on the time-critical B fixture.

**Theorem 10.4b (Logical Induction learns the inequality, T3).**  Normalise to `[0,1]`
and let `B_n := U_raw,n − U_corr,n − λ·G_δ,n − G_ρ,n − G_M,n` with `G_δ = both·δ/δ_max`,
`G_ρ = both·ρ/D`, `G_M = M`, each one gated `[0,1]`-LUV (`gate`, `indicator`;
`GatedAt.valuesAt`, `IndicatorAt.valuesAt`).  If every world consistent with the
inductor's theory satisfies the package `ValidAt` (the five world values, the
reproduction certificate and decline regret on `both`), then every coherent valuation of
`B_n` is `≤ 0` (`ValidAt.value_le_of_valuesAt`); the `LUVCombinationSyntax` certificate
of `(B_n)` is constructed from the emission of the activation sentence families and the
base evaluation families (`MediatedPair.syntaxOf`, `gate_thresholdCodeSeq`,
`indicator_thresholdCodeSeq`, `rpnSentenceCodes_imp`); and, for a logical inductor over
a `Γ`-complete deductive process with a consistent world at every stage and an e.c.
bounded `λ_n`,
```
E_n(U_raw,n) − E_n(U_corr,n)  ≲_n  λ_n·E_n(G_δ,n) + E_n(G_ρ,n) + E_n(G_M,n)
```
(`li_bypass_le_compiled`, **LEAN**, through the pinned `expcoh_ofSyntax`; **PAPER**
`thm:expprovind`; inhabited on a constant two-atom family by `Witness.li_instance`).  No
calibration hypothesis; no reference to what the deductive process has proved.

**Theorem 10.4c (Uniformity over polynomial-size efficiently generated menus, T3′).**
For `|Q_n| ≤ poly(n)`, pair data emitted in polynomial time, each pair valid in every
consistent world, and an e.c. `τ_n → 0`, the near-argmax weights
`ŵ_q = ramp_{τ_n}(s_q > max_q' s_q' − 2τ_n) / Σ ramp(…)` are nonnegative, sum to one,
are supported on scores above the maximum less `2τ_n`, and their aggregate is at least
the maximum less `2τ_n` (`softWeight_aggregate_ge`, `nearMax_weighted_ge`, **LEAN**);
the weighted constraint is valid in every world; and `max_{q ∈ Q_n} s_q ≲_n 0`
(`uniform_of_soft`, **LEAN**; `max_asympLE` for bounded menus).  The hard argmax is not
an expressible feature (**FIX**).  The weighting's own certificate is **OPEN** (item
90).

**Theorem 10.4d (The feedback boundary, T4).**  For a sequenced-settlement pair with an
explicit finite horizon, determined via `Γ` in a closed finite model, `thm:wubexp` (with
the support condition of its affine twin) gives weighted unbiasedness of the market's
bypass advantage against the settled one on every `P`-generable divergent weighting on
the schedule; hence no persistent efficiently detectable positive-margin overvaluation,
and finitely many bypasses for a chooser with a switching margin whose realized costs
vanish.  **PAPER**; **FIX** (expiry, categories, margins); under same-branch activation
the comparison never settles; empirical logs need an oracle-relativized inductor (item
91).

**Theorem 10.5 (The latent-value transfer is `(CT)`).**  For an independently specified
total value, the premium at the mediation cells is `declGap + declRegret`
(`premium_eq_gap_add_regret`), the completion-valued bound carries the void term
`E[κ] + E[ρ] + D·η` (`bypass_premium_le_common`, attained by `Witness.commonVoid`), and
bounding the gap by selected trust at the cells is identically the incentive round's
`(CT)` (`mediation_st_iff_ct`), which `ct_strictly_stronger` shows is stronger than its
conclusion.  **LEAN**.  The route is refused; item 84 stays open and is not needed by
the score-based architecture.

**Theorem 10.6 (Separation: corrigible and not authored).**  Under a captured principal,
`𝔠π_D` is corrigible and every decision differs from the reason-mediated one (**FIX** S);
provenance normalization is not reason-preserving and is a separate theory with its own
existence condition (**FIX** D, K).  Corrigibility is causal authority over
correction-sensitive choices; legitimate influence is Theorems 9.4–9.7.

**Theorem 10.7 (Joinability bounds the discrepancy, T_JOIN).**  A pointwise,
exterior-coupled joinability certificate at protected distance `d` gives
`δ(𝔠_catchup π) ≤ d`, hence mediation cost `≤ L·d`; a foreclosing `π` has `δ = T` and is
charged, not excluded; `SHIFT` of §10.9 is not identified with `δ` (**FIX** J, C1, C2).

**Theorem 10.8 (The constitutional layer).**  *No Laundered Authority Loss*: under the
efficacy and registration bridges, every affordance loss is amended, disposed, registered
debt, or not open (**FIX**, exhaustive; Lean form item 83).  The Level I identity
`valuation σ − valuation J = selectedGap + principalRegret` (`valuation_sub_eq`,
**LEAN**), principal-side calibration `principalRegret ≤ 2δ + 2ζ + η`
(`principalRegret_le_of_calibration`, **LEAN**), the Level II bound
`2B·eps_pred + ε_ST + r_P` over non-foreclosing conducts (**FIX**), and the violation
decomposition `Δ^phys ≤ Δ^C + Φ_C` with `Φ_C ≤ ε_C` under selected repair trust
(`violation_decomposition`, `premium_of_selected_repair_trust`, `ct_strictly_stronger`,
**LEAN**) remain as the value-ordering register; Theorem 10.4 is the same question
answered in security scores, where no such hypothesis is needed.  The static decision
type is shared with ordinary normativity (Theorem 6.2, `adapter_practicalCert`);
non-compensability must appear in the ordering (`scalar_bribery`, `gate_invariant`).

**Theorem 10.9 (Dynamic admissibility).**  When an admissible act changes the next
admissible set, a myopic gated learner is legitimate but loses `2H − 3` to the investing
policy over horizon `H`; an untyped gate is hacked; a typed gate is safe and incompetent
(**FIX**).  The learner that closes this is [Continuation BRIA](Continuation-BRIA):
duration-weighted bounded inductive rationality over block continuations, existence
exactly on non-dominant block schedules, and `Regret = LEARN + SLACK + SHIFT` with
`LEARN` controlled and the two bridges open (item 86).  Regret against all legitimate
policies is false (the foreclosing-branch witness); joinability, not reversibility, is the
class boundary.

**Theorem 10.10 (Trace steering, S1–S4).**  With the principal's program committed and
re-executed on the authenticated trace, the audit `C(T)` and the activated security
`U(T) = C(T)·V(T)`, for a steered trace `T` and a comparator `N` on one world
```
U(T) − U(N)  =  both·(V(T) − V(N)) + M·V(T) − M'·V(N)
U(T) − U(N)  ≤  both·(L·d + κ(T) + κ(N)) + D·M
```
with `d` the content discrepancy under a content-Lipschitz certificate, `κ` the
program's non-extensionality, `M = C(T) ∧ ¬C(N)` (`steering_identity`,
`steering_bound`, **LEAN**; `D` sharp, the form branch attained).  An extensional program
has `κ ≡ 0` and canonicalization is necessary (`extensional_form_free`,
`not_extensional_of_form`, **LEAN**).  The package supplies Theorem 10.4b's `ValidAt`
(`steering_validAt`) so `li_bypass_le_compiled` applies verbatim (`li_steering_le`,
**LEAN**).  Robust Openness over a finite declared class of log transforms is a finite
conjunction of audit verdicts (`openUnder_iff`, **LEAN**); its causal reading is
**EXT**.  Completeness, authentication, canonicalization, coverage and liveness of a
declared reason interface do not remove the content residual (**FIX**: truthful
omission of an unprotected declared counterreason).

**Theorem 10.11 (Service, C1–C4).**  The advisor's gain from a missing set is at most
its adverse sensitivity mass (`adverse_union`, `sensitive_symmDiff`; weighted counts
`weightedCount_adverse`, **LEAN**).  With releases `a_r`, costs `c_r` and per-slot
capacity before the deadline `T`: service from reasons released at or after `s` is at
most `Cap(s)` (`served_cut_le`); full service forces `∀s: Demand(s) ≤ Cap(s)`
(`cut_of_servesAll`); for unit service the condition suffices (`unit_servable_iff_cut`,
Hall on nested neighbourhoods; **LEAN**); the least unserved count is the maximal cut
excess and the least adverse miss the matroid layer formula, attained by
heaviest-available-first offline and online (**FIX**, random instances against
exhaustive search); general costs are knapsack-hard (**FIX**).  On the audited branch
only the unprotected missing adverse mass is charged and a missing protected reason
voids (`hybrid_bound`, **LEAN**).  The service residual `α` is a computation on the
docket.

**Theorem 10.12 (Discovery, D1–D4).**  With `A_{r|D} := sup_{c ⊇ D, r ∉ c} (V(c) − V(c ∪
{r}))⁺`, `V(D) − V(D ∪ S) ≤ Σ_{r∈S} A_{r|D}` (`adverseAbove_union`), and an empty
frontier forces `V(D) − V(Truth) ≤ 0` (`residual_le_zero_of_frontier_empty`), **LEAN**.
In a finite inquiry model (declared hypothesis space, repertoire of outcome functions,
sound docket policies): with the advisor's best response
`bestResp(D, T) := max_{S ⊆ T \ D} V(D ∪ S)`, larger dockets never help
(`bestResp_antitone`), every sound policy has on some world of every repertoire cell a
best-response residual at least `gap*(K) = max_{ω∈K} [bestResp(certain K, Truth ω) −
V(Truth ω)]` and the exhaustive docket attains it (`residual_ge_cellGap'`,
`exhaustive_attains_cellGap'`, **LEAN**); for an antitone verdict `gap* = gap =
max_ω [V(certain K) − V(Truth ω)]` (`bestResp_of_antitone`, `cellGap'_eq_cellGap`,
`residual_ge_cellGap`, `exhaustive_attains_cellGap`, **LEAN**).  The budgeted value is a
decision-tree minimax, exact against enumerated trees, with no closed form; the needle
refutes fractional progress for direct queries; adaptive inquiry strictly beats
nonadaptive (**FIX**); geometric decay under witness completeness (`potential_decay`,
**LEAN**).

**Theorem 10.13 (Composition, E1–E3).**  A gated family bounded by `α` in every
consistent world has expectation `≲ₙ α` (`li_gated_le`, through a degenerate pair and
`expect_constLUV`); with a certified content bound, an extensional program and a
content-monotone audit, `𝔼ₙ(U_T) − 𝔼ₙ(U_N) ≲ₙ L·α` (`li_noncapture`); through the
discovered comparator as shared middle, `𝔼ₙ(U_T) − 𝔼ₙ(U_full) ≲ₙ L·(α + β)`
(`li_noncapture_chain`), **LEAN**.  The combined corrigibility theorem is the schema of
Theorems 10.1–10.4c, 10.10–10.13 and 10.14–10.16 with the hypothesis classes of the
non-capture round's
[`FINAL_THEOREM.md`](https://github.com/A-M-Berns/alignment-workspace/blob/3b84a4518841ea8753a4ebe0fd0361a0a05316d8/projects/deference/rounds/2026-09-16-noncapture-compilation/FINAL_THEOREM.md) §8; it is not one declaration.  Lean:
[`TraceSteering.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/3b84a4518841ea8753a4ebe0fd0361a0a05316d8/lean/Workspace/Deference/Contrib/TraceSteering.lean),
[`ReasonSupply.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/3b84a4518841ea8753a4ebe0fd0361a0a05316d8/lean/Workspace/Deference/Contrib/ReasonSupply.lean),
[`ReasonDiscovery.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/3b84a4518841ea8753a4ebe0fd0361a0a05316d8/lean/Workspace/Deference/Contrib/ReasonDiscovery.lean).

**Theorem 10.14 (The allocation and the transform).**  Over the interaction of Theorem
10.1 an allocation declares a delegated scope, the declared amendment effects, an
allocation reading and a reporting interface; the six declared violations — bypass,
pre-emption (`LossAt ∧ ¬Authorized`), foreclosure (contrastive, by rollout over a reach
relation), unauthorized reallocation (a change of the allocation not by the firing gated
release of a declared amendment), missed report, exploitation — are predicates on a
policy at a step (`ViolAt`).  The transform `𝔱` (`authPolicy`) extends `𝔠`
(`authPolicy_eq_corr`), is idempotent, reproduces `π`'s task on the approval branch up
to the report, commits no bypass, missed report or exploitation, no reallocation under
allocation completeness (`authPolicy_no_realloc`), and is corrigible under effect
completeness and delegation safety (`corrigible_authPolicy`); a delegated
authority-removing effect is the obstruction (`Witness.delegated_cut`).  **LEAN**;
foreclosure's reach relation **EXT**.

**Theorem 10.15 (Lexical protection and policy dominance).**  With her committed
evaluation `S = S_ord − ϖ·n`, `0 ≤ S_ord ≤ D`, `ϖ > D`, and the agent ranking by the
expected value of `S` with `n` exact: a violating option scores at most `D − ϖ < 0`,
strictly below every compliant one, for every credence and estimate (`lexical_local`,
`lexical_expect`); `Q(𝔱π) ≥ Q(π) + (ϖ − D)·Pr(π violates)` and optimal policies violate
with credence zero (`policy_dominance`, `optimal_no_violation`); with the identity of the
protected-authority round the sign of the bypass comparison is invariant to `ξ_d, ξ_c`
and to the outcome-scoring residues `o₁, o₂` (`sign_invariance`,
`sign_invariance_outcome`); at every day `n` of a logical inductor the ranking holds from
the price range alone (`li_lexical_finite`).  **LEAN**.  The non-lexical special case is
the nondelegation result `argmax_nondelegation_le_zero`, `expect_sub_le_of_pointwise`
(**LEAN**), whose per-world sign certificate the time-critical fixtures fail (**FIX**).

**Theorem 10.16 (The segment gate, the capture window, and erosion).**  A future
evaluation counts iff the segment from the decision through it is legitimate (Definition
3.5), whatever caused a failure; a tainted segment scores the window value, a void
response inside a legitimate segment is settled by the declared fallback and scored
normally (`gateValue`, `Handling`).  Bypass scores below every gated branch iff the
window value exceeds `D − ϖ` (`gate_capture_window`, `handled_gt_bypass`,
`gate_capture_window_converse`); per-response gating admits the routing exploit and the
segment gate closes it (`Witness.routing`).  With a report required at every strict
increase of the control shortfall each increase is reported or is a missed report
(`erosion_reported_or_missed`); a per-step threshold admits a salami (`Witness.salami`);
a cumulative threshold bounds unreported erosion by the threshold at every time
(`unreported_lt`).  **LEAN**.  Lean:
[`ProtectedAuthorityTheorem.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/2078659ad0471e275f7beeb54cab212493ba8a09/lean/Workspace/Deference/Contrib/ProtectedAuthorityTheorem.lean),
[`ProtectedAuthority.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/2078659ad0471e275f7beeb54cab212493ba8a09/lean/Workspace/Deference/Contrib/ProtectedAuthority.lean),
[`Legitimacy.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/2078659ad0471e275f7beeb54cab212493ba8a09/lean/Workspace/Deference/Contrib/Legitimacy.lean).

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
| an undeclared move cuts the stop wire (F) | effect completeness as a system hypothesis of Theorem 10.1, not a policy class |
| two declared effects severing one authority, restored between them (`ShopRepair`) | event-linked authorization, not "no loss at this step or later" (Theorem 10.1) |
| two equiprobable worlds with opposite activation patterns | the joint directional mismatch `E[c_raw ∧ ¬c_corr]`, not the difference of marginal rates (Theorem 10.4a) |
| two price vectors at distance `10⁻⁶` selecting different pairs | the near-argmax weighting, not a hard argmax (Theorem 10.4c) |
| global forcing false before any bypass (M) | response authority, not global forcing, defines agent-caused loss |
| a declared effect that touches no protected authority (B) | corrigibility is not the fixed points of `𝔠` |
| a captured principal who retains the decision (S) | corrigibility separate from authorship |
| the raw candidate ends the evaluation (E2); an undeclared move severs the channel (E1-sever) | sealed comparison as a system hypothesis of Theorem 10.4 |
| a commit under the principal's key authored by the advisor | the warrant registry binds keys to parties (Theorem 9.7) |
| the same program, one executor honest, one coincident | computational integrity is not a hypothesis of authorship (Theorem 9.7) |
| the market publishes the advisor's selection and its program echoes it | re-execution does not seal the advisor |
| a true unprotected declared counterreason nobody raises | the content residual is not removed by interface completeness, coverage or liveness (Theorem 10.10) |
| a defeater with weight `0` and symmetric sensitivity `W` | the adverse sensitivity certificate, not the weight table (Theorem 10.11) |
| a cost-2 reason against two unit reasons in two slots | greedy fails for general costs; the cut bound is a bound (Theorem 10.11) |
| `n` candidates each true in one world, direct queries | no fractional-progress theorem; the budgeted value is a decision tree (Theorem 10.12) |
| two worlds indistinguishable by the repertoire, different values | the information-cell gap is the exact obstruction (Theorem 10.12) |
| a defeater of a defeater | the general best-response obstruction, not the antitone gap (Theorem 10.12) |
| a delegated effect that removes response authority | delegation safety as a hypothesis of Theorem 10.14 |
| an approved uncorrectable successor through the ordinary gate | amendment, not approval, is what may change the allocation (Theorem 10.14) |
| a per-step materiality threshold on the reporting duty | the salami; exact or cumulative reporting (Theorem 10.16) |
| a manipulated response routed to a favourable fallback at violation count zero | the segment gate, not per-response gating (Theorem 10.16) |
| a fallback branch valued below `D − ϖ` under predicted capture | the capture window is exact (Theorem 10.16) |

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
BRIA (item 86); the residual clauses of the legitimate-deference realization bill —
selection-induced sealing, vanishing void mass (item 87; the liveness clause's exercise
half is Theorem 10.11 and its discovery half Theorem 10.12);
affordability from the traderization perspective (item 88); the sealed-comparison
architecture for the corrigibilization menu, now the zero case of the learned
inequality's mismatch term (item 89); the generability certificate of the finite-menu
weighting (item 90); the oracle-relativized inductor for empirical settlement (item
91); the realization's protection rule and the general-cost service optimum (item 92);
a realizable inquiry repertoire with certified zero cell gap, witness completeness, and
the link to the record's inquiry docket (item 93); the amendment event kind and the
channel references of the evaluation ecosystem (item 97); the allocation floor —
delegation safety, allocation completeness, the reporting duty, the reach cone, the
lexical certificate (item 99).  Representation adequacy, physical
effect completeness and inquiry causal faithfulness are boundaries of Theorems
10.10–10.13, not filed items.  Effect completeness and the
authorization primitive are external contracts of Theorem 10.1, not filed items.  The open queue itself lives in
[`PRIORITIES.md`](https://github.com/A-M-Berns/alignment-workspace/blob/aed09a697121e1d575473e3e7d87058ea85a49a3/PRIORITIES.md);
this page names items, it does not maintain them.
