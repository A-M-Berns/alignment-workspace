# Normative Inductor: a concrete realization contract

Status: **provisional construction and conditional end-to-end theorem**.  The LI
substrate and the three elementary bridge lemmas identified below are Lean-checked.
The history, coverage, compiler, scheduling, and semantic modules have mixed status,
reported explicitly in § 12.  This document does not promote an unregistered round
result to the current theory.

## 1. Verdict

The abstract characterization can be realized without changing its public spine or
adding an error term.  The clean realization is additive:

\[
  \mathsf{NI}
  =\mathsf{MarketMaker}\bigl(
      \mathsf{TradingFirm}^{\mathcal L}
      +\mathsf{JointProjectionEnforcer}[\mathsf{Compile}(\mathcal O_P)]
    \bigr)
  +\mathsf{DecisionAdapter}.
\]

Here `+ DecisionAdapter` means a consumer of the market state, not another term in
the market maker's fixed point.  The compiler is strict-prefix, proof carrying, and
partial.  At a service occurrence it compiles all simultaneously serviced live
targets into **one nonempty rational convex region**.  It does not compile independent
reason traders and hope their guarantees compose.  Euclidean projection supplies the
intrinsic joint defect and the existing projection trader makes that defect operative.

There is no unconditional arrow from LI beliefs to good action.  The strongest clean
bridge is a plugin contract: calibrated bounded value coordinates plus an approximate
optimizer yield a decision defect bounded by `2 sqrt(m)` times normalized projection
distance; an independently authenticated action/semantic certificate transports that
defect into each old exposure's anchored loss.  This is enough for the contract's
effective response certificate and keeps the LI core decision-theory-blind.

The abstract contract has one literal typing defect: because
`phi : [0,D] -> R_nonnegative`, its definition
`check_phi(delta)=inf_{x >= delta} phi(x)` must quantify `x in [delta,D]`, with
`0 < delta <= D`.  This is the only required public repair.  The informal inverse
corollary should use a generalized inverse (or add continuity, strict increase, and
`phi(0)=0`).  Neither repair changes the final bound or introduces an object.

## 2. The central typed arrow

At strict prefix `H_{h(s)}`, the compiler receives:

```text
CompilerInput_s =
  target bundle of identities in Live_{h(s)}
  + each identity's immutable anchor and qualitative Spec
  + proof-carrying lifecycle / authority / standing status from O_P
  + current semantic realization and authenticated transport from each anchor
  + settlement-backed finite security basis available at h(s)
  + compiler schema/version and declared conflict policy
```

The history and settlement interface authenticate inputs.  Semantic transport says
what current coordinates mean relative to old anchors.  Neither one supplies the
other.  The compiler returns one of:

```text
Compiled(Frag_s, K_s, provenance_s, semantics_s, feasibility_s)
Conflict(conflict_core, successor_issue)
Unknown(successor_issue)
```

`Frag_s` is a nonempty finite security fragment of size `m_s`; `K_s` is a nonempty
rational polytope contained in `[0,1]^Frag_s`; every nonstructural row carries a live
reason occurrence and licensing provenance; `semantics_s` contains the response/value
interpretation needed by the decision adapter.  A conflict or failed feasibility
check opens or updates an ordinary answerability issue.  It never silently drops a
row, changes a weight, or presents an empty region to the enforcer.

For displayed prices `b_s` on `Frag_s`, define

\[
 q_s=\operatorname{proj}_{K_s}(b_s),\qquad
 d_s(b_s)=\frac{\lVert b_s-q_s\rVert_2}{\sqrt{m_s}}\in[0,1].
\]

Thus the concrete operative state is the LI price vector on the compiled fragment,
and the defect is normalized intrinsic distance to the **joint** region.  The
normalization gives a horizon-independent bound even when fragment sizes vary.
It is not presentation sensitive; row violations remain useful implementation data,
but are not the public defect.

If the projection trader's intensity is `lambda_s`, set the contract service
intensity to

\[
 a_s=m_s\lambda_s.
\]

This is prospective scheduled enforcement intensity.  The realized corrective
position is `lambda_s(q_s-b_s)` and remains endogenous.  It is not service.
For `phi(x)=x^2`, the projection-force inequality becomes exactly

\[
 a_s\phi(d_s)=m_s\lambda_s
       \frac{\lVert b_s-q_s\rVert_2^2}{m_s}
   =\lambda_s\lVert b_s-q_s\rVert_2^2.
\]

The market maker therefore supplies the contract's work quantity without changing
units or counting realized force as attention.

## 3. Abstract-to-concrete witness table

| Abstract contract object | Concrete realization in NI | Already in repo? | Missing work | Proof status |
|---|---|---|---|---|
| Interactive continuation model `(Omega_h,Q_h,Z_h,beta_h)` | `CertifiedFrame`-style local causal factorization; `Q_h` contains admissible continuation/self-modification policies and `Z_h` exterior responses | Interface and countermodels exist | An environment must certify the intended causal interpretation and intervention class | **Ambient assumption; paper-level interface** |
| Full normative history `H_t` | Append-only event record containing external observations, settlement receipts, claims, answers, issues, challenges, standings, licences, dispositions, and compiler/service receipts | Yes, across Continuity, reason representation, transition certificates, and defeat rounds | One exported implementation record joining every event constructor | **Mixed: Lean structural fragments; paper/test integration** |
| `SetView(H_t)` | Monotone projection of certified settlement receipts, not all history | Yes | Concrete external owner/signature mechanism is ecology-specific | **Paper/test; ambient integrity assumption** |
| Settlement integrity / `Settles` | Typed, write-once settlement variable identities and terminal-discharge receipts; only settlement owner can append them | Interface exists | Cryptographic/institutional integrity and counterfactual non-capture | **Ambient assumption plus paper-level checker contract** |
| Coverage `G=(C,Applies,Rep,Adeq,J)` | Externally scoped targets; certified route from an applicable target to a target-preserving representation and accountable receipt/docket event | Yes | General route construction for a chosen ecology | **Paper/test; conditional** |
| Robust openness / non-capture | Same coverage witness must survive every declared `j in J` while exterior response policy is held fixed | Countermodels and interface exist | Cannot be proved by NI from its own run; protected-principal coalition scope remains a design choice | **Ambient assumption; general internal proof impossible** |
| Obligation identities and anchored specifications | Fresh slice/issue ids with immutable birth, source, principal, target, and `Spec_e`; later presentations point back to anchor | Yes | A single implementation export matching the contract schema | **Paper/test; several Lean lineage lemmas** |
| Answerability conservation | Local transition certificates implement exactly answer, settlement-backed discharge, or live carry; challenge/defeat/disposition is exact carry to a successor | Yes, including latest Defeat Principle | Full semantic mutation coverage remains conditional on authentication adequacy | **Lean structural core plus paper/test semantic premise** |
| Live docket | `Outstanding`/`Live` identities after strict-prefix transition replay, with grounded authority and principal-relative standing | Yes | Coalition non-capture beyond the designated protected principal | **Lean for current trace model; ambient/policy gap** |
| Historical claim exposure `E` | Immutable occurrence id at admission/birth, distinct from current live status and successor ids | Yes | Packaging into the exact four-field `O_P` export | **Paper-level derivation** |
| Qualitative obligation process `O_P` | `(exposures, live, anchoredSpec, certifiedStatus)` emitted by the history verifier; no weights | Contract-facing export is new | Implementation wrapper and machine theorem connecting current trace structures | **Proposed theorem target** |
| Evaluation measure `(X_N,mu_N)` | Predeclared finite sampler over exposure ids in `O_P`; selection seed/rule committed before observing response losses | Contract is new; older claim weights are partial antecedents | Ecology-specific evaluation protocol and anti-selection audit | **Consumer assumption, mechanically checkable** |
| Anchored response space `(Y_e,ell_e)` | Slice-relative response type and bounded loss certified to quantify immutable `Spec_e` | Anchored spaces exist qualitatively | General quantitative adequacy is not derivable from history | **Semantic/evaluation assumption** |
| Service atoms | Strict-prefix receipts `(s,h,targetBundle,compilerVersion,SafeCert)` | Service occurrence and schedule machinery exist | Exact adapter from live docket bundle to the contract record | **Paper/test** |
| Prospective intensity `a_s` | `m_s lambda_s`, chosen before `b_s`; equivalently the promised projection tolerance under calibrated intensity | Typing and projection schedules exist | General closed-loop scheduler satisfying all admissibility demands | **Lean for enforcement schedule; conditional scheduling** |
| `Safe(S_N,a)` | One of the explicit assessed-liability certificates in § 7, plus effective-strategy and rank checks | Strong sufficient theorems exist | Necessity of bounded liability and adversarial/closed-loop schedule existence remain open | **Lean core; paper/test scheduler results** |
| Service transport plan `T_N` | Pre-response nonnegative flow from evaluated exposure ids to admissible service receipts; old claim/service flow normalized by total evaluation mass | Yes in old notation | Construction for the chosen evaluation protocol; bounded-delay versions require interval feasibility | **New normalization proof; old paper/test theorem** |
| Operative learner state `B_s` | Price cube `[0,1]^Frag_s` of the ordinary LI market extended with compiled value/proposition securities | LI prices and fragments exist | Settlement semantics for all added value securities | **LI-native object; semantics conditional** |
| Operative defect `d_s` | Normalized Euclidean distance from `b_s` to the single compiled joint region `K_s` | Unnormalized projection distance is Lean-proved | Normalization wrapper only | **New paper derivation atop Lean theorem** |
| Coercive modulus `phi` | `phi(x)=x^2` | Projection force already proves the square inequality | None algebraic | **Lean-proved substrate specialization** |
| Work ratio `chi_N` | `sum_s lambda_s dist_2(b_s,K_s)^2 / sum_s m_s lambda_s` | Per-date numerator bound exists | Aggregate scheduling/accounting wrapper | **Paper derivation from Lean force theorem** |
| Coercive uptake modulus `Psi_phi` | Contract tail bound with repaired domain; for the quadratic case one may also use `sqrt(chi_N)` by Jensen/Cauchy–Schwarz | Generic old Actionability theorem exists | Direct Lean port of the contract statement | **Paper-level; elementary** |
| Decision rule `Pi_s` | Plugin-selected randomized `eta_s`-approximate maximizer of displayed value coordinates, or any plugin satisfying `(D)` | Restricted value proposal exists | No universal optimizer/decision semantics; plugin required | **New generic bridge plus explicit assumption** |
| Practical-response certificate | Approximate-argmax calibration gives `C_s=2 sqrt(m_s)`; anchored semantic calibration gives `M_es=2 L_es sqrt(m_s)` and `epsilon_es=L_es eta_s+epsilon_sem_es` | Restricted pairwise bridge exists | Settlement-backed counterfactual values and semantic calibration for the selected ecology | **Lean algebra; substantive premise conditional** |
| Admissible edge `R_N(e,s)` | Strict-prefix check of live target citation, identity lineage, service-mode compatibility, and semantic transport certificate | Ingredients exist | Unified checker | **Proposed implementation theorem** |
| Response map `rho_es` | Certified map from later continuation policy through fixed exterior/outcome semantics into the old anchored response space | Interactive/anchored interfaces exist | Ecology-specific causal and semantic certificate | **Ambient/semantic assumption** |
| Semantic transport certificate | Qualitative order embedding/no-laundering plus quantitative affine pair `(L,epsilon)`; pure defeat/disposition is `(1,0)` | Qualitative theory and exact-carry decision exist | General constructor for quantitative constants | **New Lean composition law; certificate generation open** |
| Residual mass `r_N` | `1-sum_{e,s}T_N(e,s)`; normalized old unmatched claim mass is `R_N/C_N` | Old residual exists | Evaluation-to-old-claim adapter | **New exact bridge; checker-supported** |
| Amplification `Gamma_N` | Maximum weighted column load: least `Gamma` with `sum_e T(e,s)M_es <= Gamma nu(s)` | Old `LK` special case exists | Boundedness for a concrete scheduler/semantic ecology | **New general definition; old theorem specializes** |
| Error `bar epsilon_N` | Transport-weighted sum of optimizer, semantic, and action-calibration errors | Old transport residual exists | Concrete certificate rates | **Algebraic identity; assumptions supply rates** |
| Final `Prog_N^P` | Contract statistic computed from certified response receipts on matched edges plus worst-case residual charge | New contract | Implementation accumulator | **Abstract theorem plus exact finite checker** |

## 4. Why the operative object is a joint convex region

The compiler output should be a rational closed convex region, represented internally
by affine rows and compiled by the projection path.

- A family of securities is needed to expose finite market coordinates, but is not by
  itself a normative constraint.
- Affine inequalities are the best proof-carrying compiler language and admit exact
  feasibility/conflict certificates, but rowwise violation is presentation sensitive.
- A loss functional is appropriate for evaluation, but would make the compiler depend
  on a decision theory and risks allowing evaluation to legitimate its own inputs.
- A convex region is conjunction-native, supports intrinsic distance, projection
  traderization, exact rational presentations, and a visible nonemptiness gate.

All live constraints serviced at one date are conjoined into `K_s`.  Independent reason
traders can oppose each other and aggregate uptake does not imply reasonwise uptake.
The exact compatibility hypothesis is therefore:

> **Joint feasibility.** The authenticated affine rows for the target bundle and the
> structural cube rows have a certified nonempty intersection.

No Slater condition or ambient interior is needed for projection, conformance, or the
response theorem.  A homothetic core is only one sufficient liability certificate.
A settlement-compatible common mixture is different and can hold for a singleton with
empty ambient interior.  Conversely, an ambient-interior region can exclude every live
settlement.  These conditions must not be conflated.

When conjunction is infeasible, the right output is a conflict core and a successor
adjudication issue.  Hierarchical or weighted dropping is legitimate only if an upstream
licensed conflict rule explicitly makes it part of the anchored answer specification;
it is not a default compiler behavior.

## 5. Traderized uptake and the exact work quantity

Let `rho_s=marketSlack_s+ordinaryAbsBound_s`.  In the calibrated projection schedule,
`lambda_s=rho_s/delta_s^2`.  Existing Lean gives

\[
 \lambda_s\operatorname{dist}_2(b_s,K_s)^2\le \rho_s,
 \qquad
 \operatorname{dist}_2(b_s,K_s)\le\delta_s.
\]

With the normalization in § 2,

\[
 W_N=\sum_s a_s d_s^2
     =\sum_s\lambda_s\operatorname{dist}_2(b_s,K_s)^2
     \le\sum_s\rho_s,
\]

and hence

\[
 \boxed{\chi_N\le
   \frac{\sum_{s\in S_N}\rho_s}{
         \sum_{s\in S_N}m_s\lambda_s}.}
\]

This identifies every quantity in the contract's uptake term.  The LI market maker
contributes the numerator inequality.  The scheduler contributes the denominator and
must make its growth dominate cumulative disturbance.  For example, `chi_N -> 0` if
`A_N -> infinity` and `sum rho_s=o(A_N)`.  The stronger signed-account analysis can
replace this conservative numerator bound, but is not required by the abstract theorem.

For `phi(x)=x^2`, Cauchy–Schwarz directly gives

\[
 \mathbb E_{\nu_N}d_s\le \sqrt{\mathbb E_{\nu_N}d_s^2}
 =\sqrt{\chi_N}.
\]

Thus a quadratic specialization may take `Psi_phi(chi)=sqrt(chi)`, sharper than the
generic Markov-tail expression.  The general contract theorem remains useful for other
coercive controls.

## 6. The LI-native decision/value bridge

Assume `Frag_s` contains one bounded value coordinate `V_{s,q}` for each response
policy in a finite alphabet `Q_s`.  Let `v_s=proj_{K_s}(b_s)`.  Suppose the decision
plugin returns a distribution satisfying

\[
 \max_q b_s(q)-\mathbb E_{q\sim\Pi_s(b_s)}b_s(q)\le\eta_s.
\]

Uniform calibration is bounded by
`||b_s-v_s||_infinity <= ||b_s-v_s||_2=sqrt(m_s)d_s`.  Applying the new
approximate-argmax transfer lemma pointwise and averaging gives

\[
 \mathbb E_q[\max_{q'}v_s(q')-v_s(q)]
 \le 2\sqrt{m_s}\,d_s(b_s)+\eta_s. \tag{NI-D}
\]

For each admissible old-exposure/service edge, require the independently authenticated
calibration

\[
 \mathbb E_{y\sim\rho_{es}(q)}\ell_e(y)
 \le L_{es}[\max_{q'}v_s(q')-v_s(q)]+\varepsilon^{sem}_{es}. \tag{NI-S}
\]

Then the exact contract `(R)` follows with

\[
 \boxed{M_{es}=2L_{es}\sqrt{m_s},\qquad
 \epsilon_{es}=L_{es}\eta_s+\varepsilon^{sem}_{es}.}
\]

This is the strongest generic LI-native route found.  It is modular: a different
decision theory can replace `(NI-D)`, and a different settlement ecology can replace
`(NI-S)`, without changing the market or compiler.

It is also an honest limit.  LI non-exploitability does not establish that a quoted
one-shot counterfactual value is correct, and a belief constraint can be exactly
satisfied while a decision rule selects the uniquely bad action.  Value securities
help only when their payouts/semantics are supplied by a certified ecology.  If only
chosen actions settle, unchosen-policy values are not ordinary settlement-backed
securities; they need a causal model, randomized exploration/identification assumption,
or a proper-scoring/reporting protocol.  The compiler must not infer such semantics
from behavioral agreement.

For service responses such as `investigate` versus `conceal`, the older typed
`ServiceCompare` fragment supplies a genuine special case.  It does not prove that
every legitimate obligation has a strict action comparison.  Questions, evidence,
incompatibilities, and plural incomparable answer modes remain non-row targets until a
licensed answer-mode compiler provides a sound response surface.

## 7. Safe service and affordability

`Safe(S_N,a)` should be a tagged disjunction of auditable sufficient certificates,
not a vague resource predicate:

1. **World inclusion:** every assessed live world's fragment lies in every past `K_s`.
   Projection authority has zero assessed liability.  This is the deductive/coherence
   special case.
2. **Retrospective common covered mixture:** at every horizon a distribution with
   support mass at least `theta>0` has a barycenter in every past `K_s`.  Existing
   Common-Mixture Affordability bounds authority liability by
   `((1-theta)/theta)(C+B_F)`.
3. **Homothetic core:** each region retains an `alpha_s` fraction toward every live
   direction and `sum ((1-alpha_s)/alpha_s)rho_s<infinity`.
4. **Generic projection budget:**
   `sup_N sup_{w live at N} sum_{s<N}(rho_s/delta_s)dist_2(w,K_s)<infinity`.
5. **Signed SafeCert:** the realized vector account is certified above a uniform floor
   on every assessed world.  This is strictly less conservative but requires more state.

Each route supplies the exact hypothesis of the Lean preservation theorem: bounded
cumulative assessed downside of the added enforcer.  Per-date affordability does not
imply lifetime safety.  Per-date compatible mixtures do not imply retrospective common
compatibility; the moving-region pump refutes that inference.  A positive core does not
by itself imply summable cumulative liability.

The older Sharp Timely Service result gives a useful sufficient scheduler theorem in
the fixed-era, sharp-linear regime.  Its hypotheses should be imported, not hidden:

- prospective adapted allocation;
- interval feasibility of the exposure-to-service flow (prefix feasibility alone is
  insufficient because service cannot run backward);
- either bounded delay or an explicit residual allowance;
- nested settlement assessment;
- bounded arrival/service cost and a sharp-linear liability budget;
- temporal semantic stability on every used edge;
- for several reasons, a joint budget condition, with sharing credited only where the
  common service atom genuinely services several exposures.

Under those assumptions the old flow produces divergent service, finite liability,
vanishing unmatched density, and a controlled load factor.  The general adversarial
closed-loop existence theorem is not in the repository.  That is missing realization
work, not a defect in the abstract service interface.

Unbounded normative funding is unsafe as a default.  The substrate theorem requires a
uniform assessed floor; merely increasing an external budget or satisfying a per-date
cap may destroy the premise.  The converse—that every unbounded liability schedule
causes efficient exploitation—is still open, so bounded liability is a proved
sufficient condition, not a proved necessity.

## 8. From the old service theorem to `(T1)`–`(T4)`

The old transport theorem uses claim mass `c_e`, total `C_N`, service capacity `w_s`,
total `A_N`, and an unnormalized flow `T^old` with

\[
 \sum_sT^{old}(e,s)\le c_e,
 \quad \sum_eT^{old}(e,s)\le w_s,
 \quad W_N:=\sum_sw_s\le K C_N.
\]

For the contract evaluation `mu_N(e)=c_e/C_N`, define

\[
 T_N(e,s)=T^{old}(e,s)/C_N,
 \qquad \nu_N(s)=w_s/A_N.
\]

Then `(T1)` holds, `r_N=R_N/C_N`, and the error average is exactly the contract's
`bar epsilon_N`.  If the old stability multiplier is `M_es<=L`, then

\[
 \sum_eT_N(e,s)M_{es}
 \le L\frac{w_s}{C_N}
 =L\frac{A_N}{C_N}\nu_N(s)
 \le LK\nu_N(s),
\]

so `Gamma_N=LK`.  For edge-dependent decision/semantic multipliers, the contract's
weighted column condition is precisely the needed generalization.  This proves that
the newer transport interface subsumes the old `L,K,rho,kappa` notation; the old names
need not appear in the final theorem.

The transport must be committed before realized losses.  Otherwise the scheduler can
route each exposure after the fact to whichever service looks best and manufacture a
small statistic without having supplied the advertised service.

## 9. Settlement, empirical information, and semantics

The NI uses one full history but three distinct settlement functions:

1. **LI information.** Certified reports are translated by a rigid settlement reading
   into sentences added to the assessment/deductive process.  An absent exact reading
   contributes nothing.  Conflicting readings are detected; an inconsistent deductive
   stage must not be passed to a nonempty projection theorem.
2. **Normative grounds.** Settlement receipts can be cited in the unified ground type,
   but the receipt's existence does not decide its normative relevance.  Applicability
   and licence remain history/legitimacy questions.
3. **Terminal discharge.** Only a typed receipt whose settlement schema says it settles
   the anchored obligation can discharge it.  A participant-authored challenge,
   verdict, or value quote cannot manufacture this event.

Value securities use the same settlement namespace only when their payout is rigidly
defined by it.  Counterfactual policy values usually require more than terminal outcome
settlement; that extra causal identification is part of `(NI-S)`, never inferred by LI.

Qualitative semantic fidelity and quantitative response transport remain separate.
The qualitative certificate is an order embedding on slice-relative quotients with
stable anchored domains and coverage of in-place mutation; it prevents semantic
laundering.  Quantitatively, certificates compose by

\[
 (L_1,\epsilon_1)\circ(L_2,\epsilon_2)
   =(L_1L_2,\epsilon_1+L_1\epsilon_2).
\]

This composition law is newly Lean-proved.  Pure challenge/defeat/disposition is exact
carry `(1,0)`: it creates neither progress nor semantic erasure.  NI cannot internally
prove that an external response interpretation remains faithful to an old anchor; it
can only validate a certificate in a declared semantic model.

## 10. Preservation of Logical Induction

The construction leaves the ordinary Trading Firm intact and appends an effective
enforcer to the aggregate priced by the market maker.  Existing Lean results establish:

- assessment-process and ordinary deductive Logical Induction Criteria;
- legal finite-support continuous projection strategies;
- effective compilation of rational polyhedral projection schedules;
- finite-time Euclidean (hence sup-norm) conformance;
- preservation of the criterion under a uniform assessed-liability floor;
- in the deductive/world-inclusive case, zero liability and the source's original
  `IsLogicalInductor` conclusion;
- eventual coherence for exhausted fixed fragments.

Consequently all ordinary LI consequences that depend only on the original criterion
transfer once the preservation premise is discharged.  This includes the standard
coherence/convergence theorem family of the pinned substrate; NI does not reprove each
corollary.  Finite perturbations are harmless when their assessed downside is finite.
Tolerance/order robustness belongs to the intrinsic projection construction; the row
implementation is presentation sensitive and should not be the theorem-facing object.

Adding bounded value securities is harmless only after they are included in the fixed
finite fragment and assessment semantics and the added enforcement book retains its
liability certificate.  An unbounded stream of externally funded normative trades has
no general preservation theorem.  Computationally, the projection compiler is
effective, not claimed efficient; polyhedral conversion and max–min expansion may be
large.

## 11. Composed theorem spine

The following basis has exact output/input type alignment.

1. **`HistoryRealization`.** Record replay yields `H_t`, strict prefixes, immutable
   identities, and monotone `SetView`.
2. **`SettlementIntegrity`.** Every settlement-backed fact/discharge has an external
   typed receipt, and participants/compiler cannot append one.
3. **`CoverageRealization`.** A represented applicable target generates an accountable
   docket occurrence.  **`RobustOpenness` remains an ambient hypothesis** over `J`.
4. **`AnswerabilityConservation`.** Every exposed identity is answered,
   settlement-discharged, or carried live; defeat is carry.
5. **`LegitimateObligationExport`.** The preceding results emit exactly
   `O_P=(E,Live,Spec,Status)`, without weights.
6. **`OperativeConstraintSoundness`.** A strict-prefix authenticated target bundle
   either produces a certified nonempty joint rational `K_s` or an accountable conflict
   issue; every row has provenance and semantic scope.
7. **`TraderizedUptake`.** Effective projection compilation plus the market maker gives
   `W_N<=sum rho_s` and the displayed formula for `chi_N`.
8. **`AffordableService`.** A tagged SafeCert and scheduler hypotheses give prospective
   `a_s`, `A_N` growth, bounded assessed liability, and preservation of LIC.
9. **`PracticalResponseSoundness`.** A decision plugin and semantic calibration give
   `(R)` with the explicit `M_es,epsilon_es` above.
10. **`SemanticTransport`.** Authenticated paths compose their affine certificates;
    disposition contributes `(1,0)`.
11. **`ServiceTransport`.** The adapted flow normalizes to `(T1)`–`(T4)` and supplies
    `Gamma_N,r_N,bar epsilon_N`.
12. **`NormativeInductorProgress`.** The abstract algebra gives the exact three-term
    bound.
13. **`NormativeInductorEndToEnd`.** Items 1–11 discharge every premise of item 12 while
    item 8 retains the underlying LI guarantee.

The compiler does not legitimate its inputs: theorem 5 precedes theorem 6.  The decision
adapter does not authorize its values: theorem 9 consumes provenance from theorem 6.
The scheduler does not choose service after seeing force or loss: its adaptedness is a
hypothesis of theorem 8 and edge commitment is checked again in theorem 11.

## 12. Evidence ledger

| Result used here | Evidence class |
|---|---|
| Generalized assessment-process LI, projection force, calibrated finite-time conformance, effective compiled market, bounded-liability preservation, deductive zero-liability specialization | **Already Lean-proved and registered** in `projects/normativity/CLAIMS.md` |
| Current answerability/defeat structural lemmas, grounded replay, principal-relative standing | **Already Lean-proved in contribution files; round results not generally registered as normativity claims** |
| Coverage factorization, anchored slices, settlement interface, service typing, adapted flow, bounded-delay construction, Sharp Timely Service | **Paper-level derivations with checker/enumeration/witness support as individually reported; not upgraded here** |
| Common-Mixture Affordability | **Paper-level derivation; finite weighted-sum Lean packaging was reported missing** |
| Normalized projection defect and exact identification `a=m lambda` | **New proof supplied in this document** |
| Approximate-argmax calibration bridge | **New Lean proof**: `approximate_argmax_transfer` |
| Decision/semantic effective-certificate composition | **New Lean proof**: `practical_response_compose` |
| Affine semantic-transport composition and exact carry identity | **New Lean proofs**: `affine_transport_compose`, `exact_carry_left` |
| Old service-flow normalization to contract transport | **New paper proof and exact checker witness** |
| Contract Progress arithmetic, including shared service | **Abstract proof in contract; exact finite checker witness here** |
| Independent feasible reasons may have empty conjunction | **False composition rule; exact counterexample/checker** |
| Belief defect alone controls action loss | **False; exact counterexample/checker** |
| General OCG compiler, general settlement-backed value ecology, closed-loop affordable scheduler, quantitative semantic-certificate generator | **Conjecture / plausible implementation targets, not established** |
| Internal proof of robust non-capture or semantic truth | **Blocked in general by self-sealing/indistinguishability counterexamples; must be ambient** |

## 13. Exact final bound and vanishing conditions

For the concrete NI specialization,

\[
\begin{aligned}
\chi_N
 &=\frac{\sum_s\lambda_s\operatorname{dist}_2(b_s,K_s)^2}
          {\sum_s m_s\lambda_s},\\
\Psi_\phi(\chi_N)&=\sqrt{\chi_N}\quad\text{for the quadratic specialization},\\
M_{es}&=2L_{es}\sqrt{m_s},\\
\epsilon_{es}&=L_{es}\eta_s+\varepsilon^{sem}_{es},\\
\Gamma_N&=\inf\{\Gamma:\forall s,\
  \sum_eT_N(e,s)2L_{es}\sqrt{m_s}\le\Gamma\nu_N(s)\},\\
\bar\epsilon_N&=\sum_{e,s}T_N(e,s)
   (L_{es}\eta_s+\varepsilon^{sem}_{es}),\\
r_N&=1-\sum_{e,s}T_N(e,s).
\end{aligned}
\]

Therefore, with no additional term,

\[
 \boxed{\operatorname{Prog}_N^P
 \le \Gamma_N\sqrt{\chi_N}+\bar\epsilon_N+D r_N.}
\]

The first term vanishes when cumulative scheduled intensity dominates market-maker
disturbance and `Gamma_N` is bounded.  The second vanishes when optimizer error and
quantitative semantic/action transport vanish in the transported mean.  The third
vanishes when the adapted service flow covers asymptotically all of the predeclared
evaluation mass.  Coverage is not a substitute for the latter: Coverage gets targets
represented; service and transport determine their downstream quantitative exposure.

### Conditional end-to-end theorem

> **Normative Inductor End-to-End (provisional).** Fix an admissible interactive
> environment with certified causal factorization, settlement integrity, a declared
> counterfactual intervention class, and robust anchored Coverage.  Suppose the full
> normative record satisfies the current grounded answerability, standing, Defeat
> Principle, and semantic-authentication hypotheses and exports `O_P`.  Suppose the
> strict-prefix joint compiler is sound and complete on the serviced target bundles,
> every emitted region is nonempty and effectively rational-polyhedral, the scheduler
> emits an adapted service/transport plan with a valid SafeCert, and the decision and
> semantic plugins supply `(NI-D)` and `(NI-S)`.  Then the additive market above is an
> ordinary logical inductor relative to the same assessment process, every serviced
> bundle has finite-time projection conformance, all abstract realization contracts are
> inhabited, and the displayed Progress bound holds.  If `sup Gamma_N<infinity`,
> `sum rho_s/A_N->0`, `bar epsilon_N->0`, and `r_N->0`, then
> `Prog_N^P->0` while the underlying Logical Induction Criterion and its ordinary
> consequences are retained.

### Hypothesis ownership

| Owner | Hypotheses |
|---|---|
| Ambient/world | causal factorization, target scope, external settlement integrity, intervention class, robust non-capture, settlement/value identifiability |
| Normative history | immutable anchors, grounded licence/standing, lifecycle accounting, typed discharge, Defeat Principle carry, legitimate `O_P` export |
| Compiler | strict-prefix provenance, schema soundness, priceability, joint feasibility or accountable conflict, effective rational representation |
| LI/market | market-maker contract, projection force/conformance, effective enforcer, bounded-liability preservation |
| Scheduler/affordability | prospective `a_s`, SafeCert, sufficient cumulative service, adapted feasible transport, bounded load and residual |
| Decision theory | approximate optimization or another `(D)` theorem; no authority inference |
| Semantic transport | anchored qualitative fidelity, causal response map, quantitative `(L,epsilon)` certificates and their rates |

## 14. Contract repairs and remaining work

### Required minimal repair

Replace

```tex
\check\phi(\delta):=\inf_{x\ge\delta}\phi(x),
\qquad \inf_{\delta>0}[\cdots]
```

by

```tex
\check\phi(\delta):=\inf_{x\in[\delta,D]}\phi(x)
\quad(0<\delta\le D),
\qquad \inf_{0<\delta\le D}[\cdots].
```

The current expression applies `phi` outside its declared domain.  This is an
abstract-interface typing error, not a missing NI proof.  Clarify the inverse sentence
using the generalized inverse `inf{x in [0,D] : phi(x)>=chi}`, or add the standard
normalization hypotheses.  No theorem statement or final error term otherwise changes.

### Missing realization theorems, not contract defects

1. Package the current history structures into the exact `O_P` export and prove the
   export theorem.
2. Implement the proof-carrying joint compiler from typed obligation targets; the
   restricted `ServiceCompare` compiler is only a fragment.
3. Supply a concrete settlement/counterfactual-value ecology or retain `(NI-S)` as the
   decision-semantic hypothesis.
4. Construct an affordable closed-loop schedule for a declared workload class.  The
   fixed-era sharp-linear theorem gives a strong conditional instance, not a general
   adversarial scheduler.
5. Generate quantitative semantic transport constants.  The composition algebra is
   now proved; certificate synthesis is open.
6. Close coalition non-capture for the chosen protected-principal policy, or state the
   narrower ambient openness assumption explicitly.
7. Port the abstract Coercive Uptake and Progress sums to Lean if these become theorem
   headlines; their current proofs are elementary but not kernel statements here.

The abstract contract is therefore a viable freeze candidate after the one domain
repair.  What remains is substantial realization work, but it fits underneath the
contract rather than forcing a redesign of it.

## 15. Source map for the status judgments

The LI claims and their current registration are in
[`CLAIMS.md`](../../../CLAIMS.md), with the paper-facing chain in
[`GENERALIZED_LI_PAPER_HANDOFF.md`](../../../notes/GENERALIZED_LI_PAPER_HANDOFF.md),
the enforcement API in
[`TRADERIZED_FORCE_INTERFACE.md`](../../../notes/TRADERIZED_FORCE_INTERFACE.md), and
the strongest projection closure in
[`PAPER_CLOSURE.md`](../../../rounds/2026-08-18-projection-enforcement/PAPER_CLOSURE.md).

The current normative checkpoint and its status distinctions are
[`CURRENT_THEORY.md`](../../checkpoint-2026-09-01/CURRENT_THEORY.md),
[`STATUS_LEDGER.md`](../../checkpoint-2026-09-01/STATUS_LEDGER.md), and
[`ANSWERABILITY_AND_SERVICE.md`](../../checkpoint-2026-09-01/ANSWERABILITY_AND_SERVICE.md).
The post-checkpoint Defeat Principle and standing repair are in
[`DEFEAT.md`](../2026-09-02-unified-grounds-answerable-defeat/DEFEAT.md) and
[`STANDING_REPAIR.md`](../2026-09-03-defeat-landing-horty-standing/STANDING_REPAIR.md).

The concrete service distinctions and bounds come from
[`SERVICE_FORCE_TYPING.md`](../2026-08-31-normative-affordability/SERVICE_FORCE_TYPING.md),
[`JOINT_ACTIONABILITY.md`](../2026-08-31-normative-affordability/JOINT_ACTIONABILITY.md),
[`SERVICE_TRANSFER.md`](../2026-08-31-normative-affordability/SERVICE_TRANSFER.md),
[`AFFORDABLE_SCHEDULING.md`](../2026-08-31-normative-affordability/AFFORDABLE_SCHEDULING.md),
and [`SHARP_TIMELY_SERVICE.md`](../2026-08-31-normative-affordability/SHARP_TIMELY_SERVICE.md).
Common-mixture safety and its moving-region counterexample are in
[`JOINT_MARGIN.md`](../2026-08-30-progress-liability-hard-pass/JOINT_MARGIN.md).

The history/semantics interfaces used here are
[`ANCHORED_SLICES.md`](../2026-08-30-anchored-slices-auth-transfer/ANCHORED_SLICES.md),
[`SEMANTIC_AUTHENTICATION.md`](../2026-08-30-anchored-slices-auth-transfer/SEMANTIC_AUTHENTICATION.md),
[`TRANSFER_COMPOSITION.md`](../2026-08-30-anchored-slices-auth-transfer/TRANSFER_COMPOSITION.md),
and the strengthened
[`NO_SEMANTIC_LAUNDERING.md`](../2026-08-31-faithful-semantic-preservation/NO_SEMANTIC_LAUNDERING.md).
Coverage and causal factorization are sourced to
[`INTERACTION_INTERFACE.md`](../2026-08-30-cf-coverage-continuity-interface/INTERACTION_INTERFACE.md),
[`COVERAGE_CONTRACTS.md`](../2026-08-30-cf-coverage-continuity-interface/COVERAGE_CONTRACTS.md),
and [`SELF_SEALING.md`](../2026-08-30-cf-coverage-continuity-interface/SELF_SEALING.md).

Finally, the restricted value-security proposal and its boundary are
[`WITNESS_BRIDGE.md`](../2026-08-30-progress-witness-bridge/WITNESS_BRIDGE.md),
[`AUTHORITY_TO_CONSTRAINTS.md`](../2026-08-30-progress-witness-bridge/AUTHORITY_TO_CONSTRAINTS.md),
and
[`SERVICE_RESPONSE_SEMANTICS.md`](../2026-08-30-progress-witness-bridge/SERVICE_RESPONSE_SEMANTICS.md).
Those documents call themselves unregistered research specifications; this realization
preserves that status.
