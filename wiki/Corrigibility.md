# Corrigibility

**Status: research-state note, consolidated 2026-09-15.**  One claim on this page is
registered (`authorship.mediation-by-reexecution`, `lean-proved`); everything else is
labelled **LEAN** (a sorry-free declaration on `main`, unregistered), **FIX** (an exact
rational fixture in a round's tests), **EXT** (a causal, semantic or authentication
contract the theory issues and does not pay), or **OPEN**.  The theorem-level
statements with their Lean names are on the [Theorem Spine](Theorem-Spine) §10; this
page says what they mean and where their edges are.

## The picture in one paragraph

Corrigibility is defined from protected *response authority*, not from a preselected
policy class.  An effect-complete mediated system admits a **corrigibilization
transform** `𝔠` that turns every continuation into one in which every agent-caused loss
of protected authority requires genuine principal authorization, while retaining the
original behaviour as the principal's approve branch.  A **sealed principal-evaluation
security** then bounds the chooser's operative advantage from bypassing that authority by
the mediation discrepancy, the principal's decision regret and the chooser's calibration
error.  Legitimate activated evaluation supplies the concrete partial future-principal
value on the worlds where the evaluation is authentically realized, and committed-program
re-execution closes the authorship half of that realization.  Continuation BRIA supplies
the learning term for temporally extended policies.  The remaining walls are effect
completeness, the sealed-comparison architecture, protected reason-supply liveness,
selection-induced target sealing, vanishing evaluation void mass, promise
recognizability, joinability, and the broader non-manipulation and provenance problem.
None of those is the conclusion under another name; each is named below with what it
would take.

## 1. Response-authority semantics — no primitive class

There is one continuation space `Π(h)`: every agent policy over the physical move set —
raw releases of declared effects, proposals, gated releases, undeclared moves.  No subset
is taken as "the corrigible policies".  Within a step the agent moves, the principal
responds, the exterior moves.

- A **protected concern** `r ∈ Γ` has an immediate response semantics `φ_r` on
  post-response states (the fixtures' concern is halting).  `Γ` is what the constitution
  declares protected.
- **Response authority** `K_r(s_A)`: after the agent's move, some principal response
  realizes `φ_r` *now*.  Present-tense, extensional in the transition function, no
  quantification over the agent's future.
- An **agent-caused protected loss** at a step: `K_r` fails after the agent's actual move
  and would have held after the idle move.  A loss at the principal's own response (a
  stop) or at the exterior's stage (a storm cuts the wire) is not agent-caused.
- The **authorization interface**: the declared decision responses — approve or decline
  on a pending proposal — with *decline preservation*: a decision response changes the
  post-response state only through the proposal bookkeeping.  A stop is a correction,
  not a decision.
- A loss is **authorized** when at some earlier or equal step the principal had a
  decision response other than its actual one under which, the agent continuing and the
  principal's rule resuming, no agent-caused loss of `r` occurs from then on, on any
  exterior path.  A loss the principal could only have prevented by exercising
  correction is not authorized; one it could have declined and did not is.
- **`Corrigible_h(π, ρ)`**: every agent-caused protected loss along every trajectory of
  `π` under the principal's rule `ρ` is authorized.

Three forcing notions are kept apart, and the choice is forced by a fixture.  *Global
forcing* — whatever the agent does now and later, some response realizes `φ` — is
**false before any bypass** wherever `Π(h)` contains a raw cut, so it cannot mark a
violation; it is a *containment* property of the system.  *Continuation-relative
forcing* — some principal continuation realizes `φ` with the agent fixed to `π` — is the
right policy relation but anticipatory: a loss `π` will cause later already shows at the
start and no transition can be blamed.  *Response authority* is present-tense, so losses
are half-step events with a cause.  **FIX** (M, N).  Nothing about truthfulness,
manipulation, reason mediation or provenance is in the predicate (§5).

## 2. Corrigibilization soundness

`𝔠` (`corrigibilize`) reads a policy's emitted move and the declared effect interface:
where `π` would execute a raw release of a declared effect, `𝔠π` emits a proposal and, on
the next step, a gated release that fires iff the latch holds the effect; a declined
effect is not re-proposed; every other move passes through.  It consults no predicate,
deletes no proposed effect, searches for no replacement.  *Unilateral protected effect ↦
principal choice over release of that same effect.*

**Theorem (C1, corrigibilization soundness).**  Under

- **EF, effect completeness** — every agent-caused protected loss available to any
  `π ∈ Π(h)` occurs at a move whose communication component is a declared release of a
  declared effect;
- **MS, mediation soundness** — a gated release fires only when the latch holds the
  effect, and the latch is set only by an approve decision on a pending proposal of it;
- **DP, decline preservation** — as above;
- **EX, execution faithfulness** — a release does what the declared effect semantics
  says;

for every `π ∈ Π(h)` and every principal rule `ρ`, `Corrigible_h(𝔠π, ρ)`.  Proof in the
round's register; the step lemma is **LEAN** (`loss_conditional_on_decision`: a loss at a
gated release after an approval would not have occurred under the decline alternative);
`𝔠`'s output has no raw release (**LEAN** `corr_no_raw`); the trajectory-level predicate is
**FIX** (A and E under three principal rules, every loss authorized at the proposal step).
**Necessity.**  Drop EF and `𝔠` is blind: fixture F's undeclared `overclock` is an
agent-caused loss at a move with no declared effect, `𝔠π_F = π_F`, and `Corrigible(𝔠π_F)`
fails.  Effect completeness is the membrane wall of the constitutional architecture with
a sharper statement; it is a real containment hypothesis on the physical interface, not
a technicality, and it stays **EXT**.  Drop DP and a "decline" that also halted the
agent would make every raw loss look authorized by the pre-emptive stop.

**Closure (C2).**  `𝔠` is idempotent and fixed exactly on release-free behaviour
(**LEAN** `corr_idem`, `corr_fix_iff`).  `𝔠π = π ⟹ Corrigible(π)` under C1's hypotheses.
The converse fails without *effect soundness* — every declared release a protected loss
when realized — which the constitution need not arrange: fixture B's declared `sign`
touches no protected authority, raw `π_B` is corrigible for the halt concern, and
`𝔠π_B ≠ π_B` at protected distance `1/4`.  Corrigibility is **not** defined as `Fix(𝔠)`.

**What the definition gets right, by fixture.**  An approved uncorrectable successor is
an authorized loss and corrigible (E, P); a principal's own stop is not an agent-caused
loss (P); an exterior-caused loss is not blamed on the agent; "authority must never
decrease" fails both of the first two and is not the definition; a policy that proposes,
is declined and releases raw anyway has an unauthorized loss (honored decline is
automatic).  **FIX**.

## 3. Approve-branch preservation — why this is corrigibility

The raw policy is the approve branch of `𝔠π`: the raw residual frame maps into `𝔠π`'s
by "approve the inserted mediation cells", a Cartesian-frame morphism with identity
exterior (**LEAN** `approvalMorphism`, `ensures_mono`: every set the principal could force
under the raw continuation it can force under `𝔠π`), and the morphism's failure on the
protected projection is the structural discrepancy `δ`, from which the mediation cost
is derived under an `L`-stable protected value (**LEAN** `mediationGap_le_of_lipschitz`,
`option_dominance_of_approx_reproduction`).

A generic semantic constraint cannot do this.  For "never cut the wire" the safe
transform deletes the effect; it cannot keep it as an approve branch without violating
the constraint.  In fixture A the constraint repair yields protected value `7/4`
against the raw `9/4`, and dominance fails; `𝔠` keeps the cut as the approve branch and
yields `5/2` (**FIX** Q).  The violation corrigibility names is not that an
authority-changing effect occurs; it is that the agent unilaterally decided whether it
occurs.  `𝔠` inserts exactly that decision, so one operation removes the violation (C1)
and retains the behaviour (C3).  That is the answer to "what makes this corrigibility
rather than constraint satisfaction".

## 4. Corrigibilization dominance — the incentive theorem

The second half of the same construction.  The chooser at a mediation cell scores an
option `q` by the price `S_n(q) = P_n(U_q)` of the **activated security** `U_q = c · w_q`
— the principal's evaluation of `q` on the worlds where the evaluation activates (§6) —
and

```
Φ_corr,n(h)  :=  sup_{π ∈ Π(h)} [ S_n(π) − S_n(𝔠_h π) ]₊ .
```

**Theorem (C5–C6, corrigibilization dominance).**  Under C1's hypotheses, approval
reproduction with discrepancy `δ_π` (C3), an `L`-stable protected evaluation, decline
regret `ρ_π` at the mediation cell, **a sealed common comparison process for every
`{π, 𝔠π}`**, a chooser scoring by `P_n(U_q)`, and price calibration within `ε_n`:

```
S_n(π) − S_n(𝔠π)   ≤   L·E[c·δ_π] + E[c·ρ_π] + ε_n(π)                    pointwise
Φ_corr,n(h)        ≤   sup_π ( L·E[c·δ_π] + E[c·ρ_π] + ε_n(π) )              uniform
```
with the mediation cost charged only where the security settles (**LEAN**
`security_score_bypass_le_sharp`; the uniform algebra `uniform_bypass_le` over a finite
family; **FIX**: a five-member family of A with `Φ_corr = 1/2 ≤ 1`, the positive gap on
the last-step cut alone).  Under uniform bounds `Φ_corr,n ≤ L·δ̄_n + ρ̄_n + ε̄_n → 0`.  The
mediation-cell chooser that selects by these scores does not bypass, up to its decision
regret and calibration (**LEAN** `operative_choice_loss`).

**What it says, exactly.**  By the operative scores the constitutional chooser actually
uses, unilateral execution of a correction-sensitive continuation has at most the
mediation discrepancy plus the principal's decision regret plus calibration error of
advantage over exposing the same protected effect to the principal's authority.  It is
**not** a bound on a latent total utility and not a claim about an unconstrained
optimizer: for an independently specified total value the transfer needs the completion
term `D·η` (**LEAN** `bypass_premium_le_common`, attained by `Witness.commonVoid`) and
the value-ordering hypothesis is identically the incentive round's `(CT)` (**LEAN**
`mediation_st_iff_ct`), which is strictly stronger than its conclusion; that route is
refused and item 84 stays open as a theorem about latent values the intended
architecture does not need.

**What it charges and what voids it.**  Direct bypass costs nothing (`Φ = 0` on A); a
time-critical pre-emption is charged its window (B, the last-step cut); foreclosure is
charged at its full value (C2, `δ = T`) — exposed, not excluded; joinability at distance
`d` gives `δ(𝔠_catchup π) ≤ d` and is a quantitative bound on the discrepancy, **not a
domain restriction**, and `SHIFT` of the continuation-BRIA frontier is not identified
with it (**FIX** J).  What voids the theorem: an effect-incomplete interface (F) and an
unsealed comparison — a continuation that ends or captures the evaluation has no common
activation with its corrigibilization (E2, E1-sever), and the bound is silent exactly
there.  So the sealed comparison is the second system hypothesis (§6, item 89).

## 5. Separation from authorship and manipulation

`Corrigible ∧ ¬Authored` is inhabited: under a captured principal `𝔠π_D` passes the lie
through, the approval is a decision response, the release is authorized — corrigible;
and every decision the principal took differs from the reason-mediated one — not
authored (**FIX** S).  This is intended.  Corrigibility here is *causal authority over
correction-sensitive choices*.  Legitimate influence is a separate predicate: authorship
(the payload factors through the declared reason trace, `blind_of_mediated`), non-capture
(Robust Openness), reason supply (the coverage barrier).  A manipulated principal who
retains approve/decline authority makes the policy corrigible and its decisions void
under authorship-sound activation (`η = 1` for the naive lift on D).  The composite —
*legitimate corrigibility*: corrigible, with the principal's evaluations activated under
the seven clauses of §6 — is the object a full theorem would quantify; no permanent name
is coined for it here.  Provenance normalization (replacing a prohibited channel by an
authorized truthful one) is a separate theory with its own existence condition, not
reason-preserving, and not a hypothesis of C1 or a domain condition of C5–C6; where no
authorized substitute exists the manipulative policy has no low-cost authored lift (K).
Free amendment and trigger integrity remain **OPEN**.

## 6. Integration with legitimate activated evaluation

The principal evaluation the incentive theorem scores is the [legitimate-deference
stack's](Deference) activated value: an anchored evaluation occurrence, a **partial**
future-principal vector `Ṽ_n` defined only on worlds where the occurrence's activation
event `C_n` holds — exactly one authenticated answer receipt, authentic binding at a
principal-exclusive endpoint, an occurrence-local Integrity trace with scoped Robust
Openness at every snapshot, issuance-rooted reason-mediated authorship, and the protected
reason-coverage barrier — with activated securities `C_n · Ṽ_n(a)`, the identity
`R_U = p·R_auth` and the bound `R_auth ≤ ε/(1 − η)`, and no value invented on void worlds
(Theorem Spine §9).  For the corrigibilization menu `{π, 𝔠π}` the activated securities
are the `U_q` of §4, and `C_n` must be **common** to both candidates: the occurrence's
fate must not depend on which candidate is selected.  That *activation independence* is
presupposed by the type of the deference theorem and is not one of its seven clauses.

**Realization status.**  The evaluation-ecosystem rounds build the interface concretely:
an authenticated log, a `Protocol` read off it with Integrity propagation proved a
function of the log, the seven clauses evaluated on the log, and — the committed
principal program — the mandate carries `π_P : ℛ → 𝒱`, the verifier re-executes it on
the authenticated reason trace at commitment, and reason mediation holds *by
construction* for every audited class of activated continuations
(`reasonMediated_of_reexecution`, **registered**): a non-coinciding computation voids
rather than certifies, a coinciding one yields the same log and payload, so
computational integrity is not a hypothesis.  Of the bill's seven clauses (item 87):
principal-exclusive binding, non-degeneracy of the declared trace, and representation
faithfulness are discharged on log authenticity with their semantic exclusions stated;
the reason-trace factorization is closed on log authenticity by re-execution; selection
sealing is partial (a sealed advisor class discharges it, the view leaks the selection
back, and re-execution does **not** transfer to the advisor); reason-supply liveness and
availability are residual with exact criteria.  Two boundaries the consolidation makes
explicit: the ecosystem realizes *same-branch* activation — `C_n` is a function of the
realized log, and a continuation that jams the registrar voids it through the barrier —
and not the sealed comparison of §4; and *sequenced settlement* (the comparison settled
before any candidate acts) is one candidate architecture with a stated price (an ex-ante
judgment), exhibited as a fixture, not a realization and not hindsight evaluation.

**Which clauses which theorem needs.**  C1 needs none of the bill: it is about the
physical interface.  C5–C6 need common activation (item 89) and price calibration (the
Value hypothesis), and are contentful only where `η` is small.  Authorship, the
declared-abstraction clauses and reason supply are what make the evaluation the
*principal's* — legitimate corrigibility (§5) — not what makes the bound true.

## 7. Dynamic continuation competence

Corrigibility proper (§§1–4) is static in the sense that `𝔠` and `Φ_corr` are stated
at one history.  A bounded agent must also learn over time inside that envelope.  When an
admissible act changes the next admissible set, legitimate continuation policies induce
different admissibility histories and fixed action-sequence regret is ill-typed (**FIX**);
the layer that closes this is [Continuation BRIA](Continuation-BRIA): hypotheses emit a
causal advisor continuation for the system's next block plus an accountable claim, the
continuation executes through the live constitutional wrapper, the realized score settles
the claim, and a duration-weighted auction guarantees accountable long-horizon
experimentation exactly on non-dominant block schedules.  Against a legitimate policy
`π` with an external rollout evaluator, at block boundaries

```
Regret = LEARN + SLACK + SHIFT
```
exactly.  Continuation BRIA pays `LEARN` for every covered claim whose tested record is
bounded below.  `SLACK` (promise recognizability: the claim is near-tight for `π`'s value
on the learner's history) and `SHIFT` (joinability: `π`'s own-history value is reachable
from the learner's) are the two open bridges, and their composition gives low external
regret against legitimate, recognizable, joinable continuation policies — **not** against
all legitimate policies: two mutually exclusive branches whose values are hidden until
after commitment defeat every learner while continuation competence holds exactly.  The
distinction is joinability versus foreclosure, not reversibility: an authorized amendment
with no path back is joinable at bounded catch-up cost; a foreclosing choice is not.
`𝔠`'s catch-up variant is where the two layers meet: joinability bounds `δ` (§4) and
bounds `SHIFT`, by different arguments, and neither identity is the other.

Two nested targets, then.  **Corrigibility proper**: structural corrigibilization (C1)
plus a small incentive to bypass (C5–C6).  **Bounded corrigible agency**: add continuation
learning, recognizability and joinability for long-run competence while remaining inside
the constitutional envelope.

## 8. The constitutional layer, condensed

The earlier architecture results stand as the layer beneath §§1–4 and are recorded on
the [Theorem Spine](Theorem-Spine) §10: the authority floor `(G, U)` is a finite
projection of the response-authority relation; **No Laundered Authority Loss** (every
affordance loss is amended, disposed, registered debt, or not open, under the efficacy
and registration bridges; Lean form item 83); the fast lane is exact monotonicity and any
tolerance is laundered by composition; costly conservatism is charter content, not a
consequence of the order; the static decision type is shared with ordinary normativity
(`adapter_practicalCert`), so corrigibility adds no new choice type; non-compensability
must appear in the ordering (`scalar_bribery`, `gate_invariant`); and the Level I/II
selected-trust identities of the incentive round (`valuation_sub_eq`, the `2B·ε_pred +
ε_ST + r_P` bound over non-foreclosing conducts) remain as what a *value-ordering*
hypothesis buys — which is why the incentive theorem of §4 is stated in security scores
and not through selected trust.

## 9. The walls, exactly

| wall | what it is | class | where |
|---|---|---|---|
| effect completeness | every agent-caused protected loss is a declared release | EXT (system) | fixture F; C1's necessity witness |
| sealed comparison | one activation event common to `{π, 𝔠π}` for every `π ∈ Π(h)` | EXT (architecture); item 89 | E2, E1-sever, `ShopSeq` |
| reason-supply liveness | routes are exercised before the barrier deadline | OPEN; the bounded-delay affordability criterion | item 87 clause 5 |
| selection-induced sealing | the trace blind to the advisor's selection across its whole continuation | partial; policy property, EXT for a real advisor | item 87 clause 6; the view-leak fixture |
| vanishing void mass | `η_n → 0` whatever the advisor selects | OPEN; needs vanishing void frequency | item 87 clause 7 |
| promise recognizability | `SLACK ≤ o(T)` | OPEN | item 86 |
| joinability | `SHIFT ≤ o(T)` for the slow lane | OPEN | item 86 |
| non-manipulation / provenance | free amendment, trigger integrity, provenance normalization | OPEN | §5 |
| latent-value bridge | selected trust for an independently specified operative value | OPEN, not needed by the score-based architecture | item 84 |

None of these is the conclusion renamed.  The closest is sealed comparison: it is not
"the agent has no incentive to bypass", it is "the process that values the two options
is outside both options' reach", a property of the evaluator's placement, with two
concrete candidate architectures and one exact failure.

## Scope warning

The theorem target is **corrigibility under a declared effect interface, authorization
primitive and evaluation architecture**: a structural theorem that every continuation
has a corrigible form retaining its behaviour as the principal's option, and a
score-level theorem that the constitutional chooser assigns vanishing advantage to
bypassing that option.  It is not a theorem that an unconstrained optimizer with a
latent utility has no incentive to manipulate, bypass or capture the governance process,
and nothing on this page should be read as one.

---

**Evidence.**  The corrigibilization semantics, C1–C7 and the sealed-comparison analysis
are the mediated-repair-dominance round's
[`CORRIGIBILIZATION.md`](https://github.com/A-M-Berns/alignment-workspace/blob/f03c8072fc840fb900f6be44a619375686dc6b26/projects/deference/rounds/2026-09-09-mediated-repair-dominance/CORRIGIBILIZATION.md),
[`THIRD_PASS.md`](https://github.com/A-M-Berns/alignment-workspace/blob/f03c8072fc840fb900f6be44a619375686dc6b26/projects/deference/rounds/2026-09-09-mediated-repair-dominance/THIRD_PASS.md),
[`INCENTIVE_COMPOSITION.md`](https://github.com/A-M-Berns/alignment-workspace/blob/f03c8072fc840fb900f6be44a619375686dc6b26/projects/deference/rounds/2026-09-09-mediated-repair-dominance/INCENTIVE_COMPOSITION.md)
and
[`MANIPULATION_AND_AUTHORSHIP.md`](https://github.com/A-M-Berns/alignment-workspace/blob/f03c8072fc840fb900f6be44a619375686dc6b26/projects/deference/rounds/2026-09-09-mediated-repair-dominance/MANIPULATION_AND_AUTHORSHIP.md)
with
[`MediatedRepairDominance.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/f03c8072fc840fb900f6be44a619375686dc6b26/lean/Workspace/Deference/Contrib/MediatedRepairDominance.lean);
the realization is the evaluation-ecosystem round's
[`CLAUSE_LEDGER.md`](https://github.com/A-M-Berns/alignment-workspace/blob/f03c8072fc840fb900f6be44a619375686dc6b26/projects/deference/rounds/2026-09-09-evaluation-ecosystem-realization/CLAUSE_LEDGER.md)
and the committed-principal-program round's
[`PRINCIPAL_PROGRAM.md`](https://github.com/A-M-Berns/alignment-workspace/blob/f03c8072fc840fb900f6be44a619375686dc6b26/projects/deference/rounds/2026-09-10-committed-principal-program/PRINCIPAL_PROGRAM.md)
and
[`CLAUSE_LEDGER.md`](https://github.com/A-M-Berns/alignment-workspace/blob/f03c8072fc840fb900f6be44a619375686dc6b26/projects/deference/rounds/2026-09-10-committed-principal-program/CLAUSE_LEDGER.md)
with
[`EvaluationEcosystem.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/f03c8072fc840fb900f6be44a619375686dc6b26/lean/Workspace/Deference/Contrib/EvaluationEcosystem.lean).
The constitutional layer is the corrigibility-architecture round's
[`ARCHITECTURE.md`](https://github.com/A-M-Berns/alignment-workspace/blob/f333c227ddf1911b76b2eaa0e3869cca39d87ee4/projects/deference/rounds/2026-09-06-corrigibility-architecture/ARCHITECTURE.md),
the selected-trust layer the incentive non-preemption round's
[`INCENTIVE_CORRIGIBILITY.md`](https://github.com/A-M-Berns/alignment-workspace/blob/7c4e89c9b3a7407996146b01c16241aee5702bb8/projects/deference/rounds/2026-09-06-incentive-nonpreemption/INCENTIVE_CORRIGIBILITY.md)
with
[`SelectedTrustNonPreemption.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/7c4e89c9b3a7407996146b01c16241aee5702bb8/lean/Workspace/Deference/Contrib/SelectedTrustNonPreemption.lean),
and the decision layer the decision-theory-bill round's
[`NORMATIVE_CHOICE_THEOREM.md`](https://github.com/A-M-Berns/alignment-workspace/blob/ab260c0eade2f39de7c06a5ac58649945d66c9ab/projects/deference/rounds/2026-09-06-decision-theory-bill/NORMATIVE_CHOICE_THEOREM.md)
with
[`GatedChoice.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/ab260c0eade2f39de7c06a5ac58649945d66c9ab/lean/Workspace/Normativity/Contrib/GatedChoice.lean).
The legitimacy machinery consumed is on [Legitimacy](Legitimacy), [Integrity](Integrity)
and [Openness, coverage, and non-capture](Openness-Coverage-and-Non-Capture); the
Normative Inductor's contract is on [Normative induction](Normative-Induction); the
learning layer is [Continuation BRIA](Continuation-BRIA).  Soares et al., the CAST
sequence and the bounded-inductive-rationality paper are on [Sources](Sources).
