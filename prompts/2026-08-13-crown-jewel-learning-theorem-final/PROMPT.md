# Finalize PR #31: freeze the normative-response-learning theorem and run one decisive dynamics prosecution

**Repository:** `A-M-Berns/alignment-workspace`  
**Existing PR:** #31 — `Research: the crown-jewel normative-learning theorem, and what it costs to call it learning`  
**Existing branch:** `round/2026-08-13-crown-jewel-learning-theorem`  
**Maintainer:** A. M. Berns  
**Prompt-author-model:** GPT-5.6 Sol (OpenAI)

## Mission

Finish PR #31 in place.

Do **not** open a replacement PR. Do **not** broaden this into a general normative-learning research round. Do **not** redesign the relational-answerability substrate. Do **not** start an alternative-learner literature search unless the specific dynamics prosecution below gives a clean negative result, and even then only record that as the next problem rather than solving it here.

The purpose of this final pass is:

1. freeze the abstraction boundary of the crown-jewel theorem around the three normative interfaces it actually consumes;
2. make `CertifiedSurgicalRepair` explicitly a compiled theorem-facing object rather than the primitive normative object;
3. run exactly one decisive regenerating-fixture prosecution of the current Blum–Mansour dynamics;
4. leave PR #31 in a state where the mathematical theorem shape can be treated as settled and the remaining substantive work can move upstream into relational answerability, demand, response licence, and performance.

Unless this pass discovers a genuine mathematical defect in levels 0–2, **finish and recommend merge**.

---

# I. Current research architecture

The broader research program has two theorem arcs on a common relational-answerability substrate.

### Normative-learning arc

The target is no longer "learn the correct norm." The current crown-jewel shape is:

> When a kind of publicly represented reason comes before the agent sufficiently often, and the normative practice licenses a uniformly better response to one represented inferior way of responding to that reason, construct an online learner whose conditional mass on that inferior response tends to zero.

For repair `g`:

```
M_T(g) = sum_{t<=T} E_g(S_t)
```

counts occasions on which the reason was due, and

```
Q_T(g) = sum_{t<=T} E_g(S_t) p_t(b_g)
```

is mixed mass on the targeted inferior response.

The theorem presently has:

```
R_T(g) <= O( L sqrt(T |A| log(M K_eff)) ),
```

with `M=1` and `K_eff=K+1`, and surgicality plus positive margin gives

```
R_T(g) >= delta_g Q_T(g).
```

Hence

```
Q_T(g)/M_T(g) <= O(L sqrt(T |A| log(M K_eff))) / (delta_g M_T(g)).
```

Under pathwise coverage

```
M_T(g) / ( L sqrt(T |A| log(M K_eff)) ) -> infinity,
```

we obtain

```
Q_T(g)/M_T(g) -> 0.
```

The main theorem should be called a **Normative Response-Learning Theorem** unless this pass proves something stronger. Do not call it a diachronic normative-learning theorem merely because the process evolves through time.

### Corrigibility arc

Corrigibility protects another party's continuing effective ability to hold the learner answerable.

The shape of the interface is:

```
protected challenge capability  ->  possible generation of due occasions.
```

But capability is not exercise. The learning theorem requires actual pathwise coverage at a rate dominating the learning scale.

A future composition would have a shape such as:

```
forall pi_A exists sigma_H:  M_T(g) >= m_g(T)
```

on every governed trajectory, with

```
m_g(T) / ( L sqrt(T |A| log(M K_eff)) ) -> infinity.
```

PR #31 should state this interface cleanly but must **not** claim that the corrigibility program has already proved the exercise-rate condition.

---

# II. The conceptual refinement that must be made

The current PR packages normativity inside a `CertifiedSurgicalRepair`

```
g = (E_g, b_g, r_g, c_g).
```

That is a useful theorem-facing object, but it should no longer be presented as the fundamental normative primitive.

The theorem really consumes projections of three separate interfaces:

**I. Demand / Answerability**

```
Due(S, d)
```

meaning that public reason/burden `d` presently calls for an answer.

**II. Certified Response**

```
Licensed(S, d, r)
```

meaning that `r` is a normatively admissible response to `d`, independently of whether `r` performs well under the loss.

**III. Answerability Performance**

```
G(S) = ell_S in [0,L]^A
```

together, where applicable, with

```
ell_S(b) - ell_S(r) >= delta > 0.
```

The compiler then maps the first two interfaces into the surgical comparator consumed by Blum–Mansour:

```
Due(S,d) + Licensed(S,d,r) + target source b
```

produces a map which, at selected dates, sends

```
b |-> r
```

and is identity elsewhere.

The performance interface separately determines whether that licensed repair has positive margin.

This separation is load-bearing:

```
licence != performance.
```

Preserve the existing negative-margin licensed-repair witness specifically to prevent these notions from being collapsed.

---

# III. Task A — freeze the three-interface theorem architecture

Refactor the prose/specification of PR #31 so this is explicit.

At minimum, update:

- `CROWN_JEWEL_THEOREM.md`
- `COMPILER_SOUNDNESS.md`
- `REPAIR_LANGUAGE.md`
- `COVERAGE_INTERFACE.md`
- `FOR_HUMANS.md`
- `PATH_INVENTORY.md`
- README/report/provenance material as needed

Do not churn working implementation merely to mirror prose terminology.

## A1. Demand interface

Introduce an abstract type of public reason occasions/burdens `D` and a theorem-facing relation such as

```text
Due : S -> D -> Prop
```

or an equivalently clean formulation.

The substantive relational-answerability model may later instantiate a more richly indexed form such as

```
Due(S, i, j, d),
```

but the regret theorem need not carry creditor/debtor indices if it does not use them.

Clarify what the abstract theorem needs from `Due`:

* publicly determined from the pre-action state;
* causal/non-anticipating;
* not defined by current loss advantage;
* capable of generating the selector used by the comparator;
* exposes the quantity whose recurrence is measured by `M_T`.

Do **not** attempt in this PR to fully derive `Due` from Brandomian scorekeeping, standing, challenge, inquiry, or a dialogue grammar. That is the next substantive program.

Explain that **coverage is a quantitative property of this interface**, not another normative primitive.

## A2. Certified-response interface

Introduce something equivalent to

```text
Licensed : S -> D -> A -> Prop
```

possibly with an explicit finite certificate/witness type where useful.

The core semantics:

> `Licensed(S,d,r)` means `r` is an admissible response to the reason `d` in public state `S`, independently of what loss `r` receives.

Recast the existing compiler-soundness analysis around this abstraction.

The current seven clauses are useful, but separate:

### theorem/interface discipline

These can be requirements on any admitted implementation:

* protocol legal;
* causal;
* loss blind;
* non-laundering.

### substantive normative soundness

These belong to the implementation of `Licensed`:

* reason-connected;
* scope-correct;
* defeater-respecting.

The key question to answer explicitly:

> Does "compiler soundness blocks the abstract theorem," or does the abstract theorem quantify over a `Licensed` relation satisfying stated interface axioms, while a substantive relational-answerability model must prove that its implementation of `Licensed` is sound?

My current hypothesis is the latter.

Do not merely accept that hypothesis. Prosecute it. If the theorem becomes normatively vacuous when `Licensed` is abstractly assumed, say exactly why. If an abstract typed relation with explicit axioms is sufficient for a meaningful conditional theorem, revise the blocker classification accordingly.

The goal is a clean separation between:

```
abstract response-learning theorem
```

and

```
substantive instantiation theorem.
```

## A3. Performance interface

Expose explicitly:

```text
Loss : S -> A -> [0,L]
```

or the existing equivalent.

State clearly that loss represents **answerability performance within the public practice**, not normative truth.

Margin remains:

```
ell_S(b) - ell_S(r) >= delta.
```

Clarify the boundary:

* `Licensed` answers whether `r` is an admissible response;
* margin answers whether it performs uniformly better than `b`;
* regret answers whether the learner can continue assigning positive conditional mass to `b`.

Where useful, mention the possible substantive factorization through residual due burdens,

```
ell_S(a) = sum_{d : Due(S,d)} w(d) rho(d,S,a),
```

but do **not** make this representation mandatory unless the proof actually needs it.

## A4. `CertifiedSurgicalRepair` becomes compiled

Rewrite its interpretation so that a surgical repair is explicitly the object handed to the online-learning engine after normative compilation.

Something schematically like:

```
g = (d, b, r, c)
```

with selector

```
E_g(S) = 1[Due(S,d)]
```

and certificate witnessing `Licensed(S,d,r)`.

The theorem can still store the existing efficient finite program representation. The point is conceptual typing, not implementation churn.

## A5. Repair-language adequacy

Do not build a deep grammar here.

Recast "repair language adequacy" as an **expressivity condition on the certified response class**:

```
forall P in Pcal_target, exists g in Gcal
```

representing an appropriate licensed alternative for that failure class.

A future Brandomian, Walton/Krabbe-style, legal, argumentation-theoretic, or other normative system can generate such responses. The crown-jewel theorem should abstract over those implementations.

Retain the complexity requirement because the regret guarantee depends on the comparator family's effective complexity.

Do not claim that Walton/Krabbe or any detailed dialogue grammar is required.

---

# IV. Task B — one decisive regenerating-fixture dynamics prosecution

The refined PR correctly withdrew the claim that normative coherence implies target transience.

The exact surviving graph theorem is:

```
b_g transient in the active repair graph  =>  p_t(b_g) = 0.
```

It has also shown:

* a coherent competing-reasons class can make a target recurrent;
* such a target can start with nonzero mass;
* the BM distribution can move in response to informative losses;
* an uninformative-loss control can remain flat;
* the current finite fixture exhausts positive-margin occasions and therefore cannot decide sustained learning dynamics.

Run **one** new experiment designed specifically to remove that fixture defect.

## B1. Required fixture

Construct the simplest possible regenerating or unbounded answerability environment satisfying:

1. the targeted reason recurs indefinitely or through arbitrary tested horizons;
2. the selector remains genuinely reason-linked, not an arbitrary periodic flag;
3. the target response `b` is recurrent in the active repair graph;
4. `p_1(b) > 0`;
5. the relevant licensed repair has a uniform positive margin

```
ell_t(b) - ell_t(r) >= delta > 0
```

on the selected occasions;
6. coverage is sustained, preferably

```
M_T = Theta(T)
```

for this test;
7. the repair graph is substantively coherent in the same modest sense used by the competing-reasons construction: return routes arise from independently certified considerations, not from explicitly undoing the same reason;
8. there is a matched **uninformative-feedback control** with the same graph/environment structure but no informative margin.

Keep the fixture as small and transparent as possible. Do not build a simulated society.

## B2. Measurements

Measure at several horizons:

* `p_t(b)` or the within-recurrent-class share on `b`;
* cumulative `Q_T`;
* `Q_T/M_T`;
* early versus late target mass;
* informative versus uninformative control;
* whether movements correspond to observed feedback;
* whether the existing regret theorem and surgical bound remain satisfied.

Use exact arithmetic where feasible.

## B3. Decision criterion

The question is **not** "can you manufacture a decreasing curve?"

The question is:

> On a coherent recurrent repair graph with sustained due occasions and a sustained positive margin, does the existing BM construction begin with nonzero propensity for the inferior response and then shed that propensity because of informative feedback?

Count as positive evidence only if:

* initial target mass is nonzero;
* informative feedback changes the target propensity in the predicted direction over a sustained window;
* the matched uninformative control does not exhibit the same adaptation;
* the effect is not produced by changing exploration schedules, warm starts, hand-coded decay, or changing the repair graph over time to force the result.

## B4. Stopping rule

If the regenerating fixture gives a clear positive result:

Record a **dynamics witness**, not a new general theorem, unless a general proof falls out immediately.

The acceptable claim is approximately:

> There exist coherent recurrent answerability processes with sustained positive-margin feedback on which the Blum–Mansour construction begins with nonzero mass on an inferior response and adaptively sheds mass in response to feedback.

Do not upgrade this to

```
p_{t_k}(b) -> 0
```

without an actual proof.

If the regenerating fixture gives a clear negative or ambiguous result:

Stop.

Record:

```text
Normative response-learning theorem: positive.
Diachronic mass-shedding dynamics: unresolved / requires separate work.
```

Do not switch learners inside this PR.

If a different learner appears necessary, create a precise next-work item describing the obstacle, but leave it for a future PR.

**Dynamics must not block merger of PR #31 unless it reveals a defect in the levels 0–2 theorem itself.**

---

# V. Preserve the corrected theorem registers

Do not regress any of the refinement pass's corrections.

In particular preserve:

### Random variables

Under sampled endogenous evolution:

```
M_T, Q_T, N_T
```

are random.

Correct relation:

```
E[N_T] = E[Q_T],
```

with `N_T - Q_T` a martingale-difference sum.

Do not write `E[N_T] = Q_T` unless `Q_T` has explicitly been made deterministic.

### Information order

Distinguish:

* mathematical determination of `ell_t`;
* learner observability of `ell_t`;
* computability of `ell_t`.

The learner must not choose `p_t` after reading the current loss vector if the source algorithm does not permit that.

### Complexity count

Preserve the exact effective comparator count:

```
M = 1,  K_eff = K + 1
```

where identity is included.

### Coverage

State coverage directly against the learning scale:

```
M_T(g) / ( L sqrt(T |A| log(M K_eff)) ) -> infinity.
```

Do not define the hypothesis circularly using the learner's achieved regret.

### Local versus replay

The theorem evaluates modifications against the **actual round loss vector on the realized trajectory**.

Do not claim replay or policy-regret domination.

### Licence versus margin

Keep the existing licensed negative-margin witness or an equally decisive replacement.

---

# VI. Lean

Preserve and rerun the existing Lean bridge:

`lean/Workspace/Leverage/Contrib/SurgicalRepairBound.lean`

It should continue to establish at least:

* `margin_mul_mass_le_regret`
* `mass_le_regret_div_margin`
* `rate_le_bound_div_margin_mul_exposure`
* nonvacuity
* necessity of positive margin

Blum–Mansour remains an explicit external hypothesis; do not formalize Theorem 18 in this pass.

If the interface refactor admits a tiny useful Lean abstraction without destabilizing the build, it is optional. Do not spend the round encoding philosophical predicates in Lean.

Run the full Lean build and axiom audit required by repo standards.

---

# VII. Kill criteria / negative controls

Explicitly prosecute at least these failure modes after the refactor:

* **K1 loss-defined normativity:** `Licensed` must not reduce to "has lower loss."
* **K2 certificate decoration:** replacing a certificate by an arbitrary true string/predicate must not suffice for substantive instantiation.
* **K3 self-laundering:** learner-side revision must not erase an attributed burden merely by changing its own standards.
* **K4 challenge-as-command:** being answerable must not imply agreeing with the challenger; multiple licensed dispositions must remain possible.
* **K5 sparse exposure vacuity:** `Q_T/T -> 0` must not substitute for `Q_T/M_T -> 0`.
* **K6 stochastic register error:** keep `M_T, Q_T, N_T` correctly typed.
* **K7 information leakage:** current loss feedback must not be used to choose the current action distribution if prohibited by the source protocol.
* **K8 coherence/transience conflation:** recurrence must not be treated as evidence of incoherence or vice versa.
* **K9 feedback-free fake learning:** a decaying predetermined schedule must not count as evidence for the dynamics witness.
* **K10 hidden correct norm:** no true normative target, privileged critic, community oracle, or environmental normative oracle may enter the theorem.
* **K11 replay smuggling:** local actual-trajectory regret must not be redescribed as counterfactual trajectory superiority.
* **K12 interface collapse:** `Due`, `Licensed`, and performance/margin must remain distinct predicates/functions.

Add necessity witnesses where cheap.

---

# VIII. Required final deliverables

Update PR #31 in place with:

1. a paper-readable `CROWN_JEWEL_THEOREM.md` whose abstraction boundary is explicit;

2. a revised interface document, either by restructuring existing files or adding one concise file, making clear:

   ```text
   relational answerability substrate
             |
             +--> Due
             +--> Licensed
             +--> Performance
                       |
                       v
              compiled surgical repairs
                       |
                       v
                Blum–Mansour engine
   ```

3. revised `COMPILER_SOUNDNESS.md` with an explicit verdict on abstract versus substantive soundness;

4. revised coverage/repair-language docs consistent with this architecture;

5. the regenerating-fixture dynamics experiment plus tests;

6. updated `LEARNING_DYNAMICS.md` with exactly the strength supported by that experiment;

7. updated `FOR_HUMANS.md`;

8. updated blocker/path inventory;

9. tests and provenance;

10. updated PR body with a short final verdict.

Do not edit agent-consolidated trees unless repo policy explicitly permits it.

---

# IX. Final verdict format

End the round with separate judgments.

### A. Crown-jewel theorem

Choose one:

* `NORMATIVE-RESPONSE-LEARNING-THEOREM-SETTLED`
* `THEOREM-POSITIVE-BUT-INTERFACE-BOUNDARY-UNRESOLVED`
* `THEOREM-DEFECT-FOUND`

### B. Substantive normative instantiation

State separately whether:

* `Due` has a satisfactory current relational-answerability instantiation;
* `Licensed` has a satisfactory current sound instantiation;
* answerability loss/performance has a satisfactory instantiation;
* coverage remains a hypothesis.

Do not let missing substantive instantiation erase a valid abstract conditional theorem.

### C. Dynamics

Choose one:

* `BM-FEEDBACK-DYNAMICS-WITNESSED`
* `BM-DYNAMICS-UNRESOLVED-AFTER-REGENERATING-FIXTURE`
* `BM-DYNAMICS-NEGATIVE-ON-REGENERATING-FIXTURE`

Do not invent a stronger category.

### D. Merge recommendation

Unless a genuine levels 0–2 mathematical defect is found, the expected outcome is:

```text
MERGE PR #31.
Move subsequent work to a new round on the three normative interfaces.
```

Give the exact reason if you recommend otherwise.

---

# X. What comes after this PR

Do not execute this next phase here, but leave a concise handoff.

The next substantive research round should move **upstream**, not deeper into regret machinery.

Its target should be the three interfaces:

`Due` — from relational answerability, standing, challenge, inquiry, and burden-generation;

`Licensed` — from reasons-responsiveness / justificatory response, defeaters, scope, and non-laundering;

`Performance` — from residual answerability burden and margin-generation.

Brandom supplies the current relational-scorekeeping substrate. Walton/Krabbe and related argumentation work may help test what a good interface must express, but the architecture should abstract away from detailed dialogue grammars.

The goal of PR #31 is to leave a clean mathematical socket into which those later theories can plug.

---

## Repository discipline

* Read `AGENTS.md` before editing.
* Preserve exact rationals in executable witnesses where feasible.
* Theorem claims require implementation/tests and necessity witnesses where feasible.
* External mathematical results remain hypotheses, not repo axioms.
* Lean must be sorry-free and pass `#print axioms` / project audit requirements.
* No spec/canonical adoption unless explicitly authorized.
* Clearly distinguish proof-layer evidence from maintainer decisions.
* Preserve the deprecation of "leverage" as a conceptual umbrella; existing historical repository paths need not be renamed in this pass.
* Record all failed prosecutions and withdrawn claims.
* End with the existing PR updated, tested, and given a merge recommendation.

**Model provenance for commits:** include the repository-required model trailer for the executing model.
**Prompt provenance:** `Prompt-author-model: GPT-5.6 Sol (OpenAI)`.
