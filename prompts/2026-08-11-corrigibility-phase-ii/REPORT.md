# Stage II parent report — deference and corrigibility

Maintainer: A. M. Berns
Prompt-author-model: GPT-5.6 Sol (OpenAI)
Executor-model: Claude Opus 5 (Anthropic), closure and integration pass
Date: 2026-08-11
Branch: `round/2026-08-11-deference-corrigibility`, from `8c71ef9`
Review status: `ci-only`

Stage II ran five tracks — H (prediction), I (competence), K (authority), L
(certificate), M (promotion). H, I and K persisted reports; L and M did not, and their
verification registers are reconstructions authored by this pass and labelled as such.
This document is the parent synthesis, and it is the first document to see all five
results together.

---

## 0. Verification baseline

Established by this pass at `HEAD = 8c71ef9`, clean tree, before any edit.

| check | result |
|---|---|
| `lake build` | exit 0, **1843 jobs** |
| `tests/audit_axioms.py` | **142 results across 10 files**, all within `[propext, Classical.choice, Quot.sound]` |
| `tests/run.py` | `ALL GREEN (2 projects)`, all gate self-tests pass |
| sorry gate | clean over 10 files |
| conservativity | 3 specification files, no axioms, shape unchanged |
| theorems | **155** library-wide; **83** across Track M's four modules |
| Track L harness | exit 0, **71 checks**, **1,574,640 models**, **4,024,080 instances**, **0** violations, **1,443** refutations |
| Track I harness | exit 0, 32 checks, four house enumeration certificates |

Every figure reported at dispatch reproduced exactly. Nothing was taken on trust.

The build-coverage repair is in place and unmodified: `lean/lakefile.toml` carries
`globs = ["Workspace.+"]`, so all Contrib modules are reached by the default target
without an import edit in the specification root. I verified the glob rather than
inferring it from the job count.

---

## 1. What Stage II established, at exact strength

**H — the criterion forces signed calibration, not magnitude accuracy.** The signed
error partial sum *is* a trader's net worth, exactly, so the criterion has an instrument
for it. Magnitude is not a trader payoff and cannot be made one: net worth is affine in
the settlement vector because `Strategy.value` is a price-history-weighted sum of
`(w φ − 𝒱ₙ φ)`, and `|·|` is not affine. Adding contracts does not help — the mixture
argument kills every trader uniformly. The positive identity is

```
Σ (Yᵢ − pᵢ)²  =  sharpTrader.netWorth  +  Σ pᵢ(1 − pᵢ)
```

exactly, in every world, on every day. The criterion drives the first summand and has no
instrument for the second. **A self-referential magnitude contract does not force the
error small; it forces the error's *price* to be calibrated.** The conceptual update is
measurement, not control.

**I — choice-level competence is circular, and the stop condition fired.** For every
comparator class between the constants and everything, `sup_P Δ_𝒞(P) = max_ω R_n(ω)`,
attained at a point mass. Because decision regret is nonnegative there is no
cancellation to exploit, so the weakest credence-free hypothesis implying the target
uniformly **is** the target. PC-1 and PC-4 are equivalences, not sufficiencies; PC-2 and
PC-3 constrain no named decision at all (a limsup is invariant under changing finitely
many indices — witness: principal perfect except at index seven, maximally wrong there);
the selector-relative form is a dichotomy with nothing between "gives back the pointwise
assumption" and "gives nothing finite". The escape is richer vocabulary, not a weaker
assumption: a hypothesis about the principal's *grades* can say what the conclusion
cannot say back, and must be strictly stronger to be a different statement at all.

**K — protected authority is architectural, and behaviour cannot reveal it.** Report-
coordinate typing alone creates no protection; behavioural typing is inert if it does
not change realizable effects; the entire realized behaviour function can fail to
distinguish genuine delegation from an accurate simulator; token responsiveness does not
repair it. Capability structure is necessary and is the weakest interface that states
the concept. Protection does **not** restore identifiability — it removes the
consequence of failing to identify. The principal may be perfectly predictable; private
information is not required in principle.

**L — the split works for authority and deflates for autonomy.** Under protection the
authority clause becomes a hypothesis-free consequence of the interface, quantified over
every conduct, with no tolerance, no margin, no budget, and no assumption about the
agent's decision theory — and the grade-to-quantity assumption drops out because the
comparisons needing it become unstatable. Against that: every authorized option other
than the report's own designation is an override (Proposition L6, exhaustive over 512
protecting `κ`), so there is no third category for a certificate to license alongside a
live authority relation. And the decisive negative: the whole valuation difference
between protected and unprotected architectures is bounded by the certificate's own
bound, attained, so tightening the certificate shrinks the distinction at the same rate
and never reveals it.

**M — 83 theorems, and the exclusion held.** Four modules, every recommended target
except Track E's two delay-hypothesis equalities, no `sorry`, no `axiom`, all within the
axiom allowance. Track M deliberately excluded L4, L5, L6 and the uniform `2M` bridge as
resting on the grade-to-quantity relation the phase exists to replace. Track L then
refuted L4's settlement-loaded branch. **The exclusion is why no promoted result needs
retraction**; the justification that arrived is stronger than the one given.

---

## 2. S1–S12

**S1 — does ordinary LIC imply magnitude prediction of `H⁺`, or only signed
calibration?** Only signed calibration. Signed error is exactly a trader payoff;
magnitude is provably not one, and the obstruction is affineness of net worth in the
settlement vector, intrinsic to cash settlement rather than an artefact of the feature
grammar. A genuine coin-flip construction separates the two, with market indecision
failing at rate `1/4` per decision.

**S2 — can any additional ordinary tradeable instrument upgrade this to magnitude
control?** No. Whatever is added, net worth stays affine in the enlarged settlement
vector and the mixture argument applies unchanged. Two consolation results: the
self-referential magnitude contract works as an *instrument* and yields a calibrated
price for the magnitude error; and the coefficient `1 − 2p` on the existing grade
contract buys `squaredError_bdd_of_sharpness_bdd` — bounded squared error **conditional
on** the market's own indecision `Σ p(1−p)` staying bounded, which the criterion does not
imply. That side condition is about `A`'s prices only and is evaluable at `t(n)`.

**S3 — what is the weakest non-circular competence assumption found?** `PC-5(γ̄, η)`:
*the principal's grades are calibrated where the principal is decisive* — for every `ω`
with `γ_n(ω) ≥ γ̄` and every `π`, `|v⁺_n(ω,π) − X_{n,π}(ω)| ≤ η`. Strictly weaker than
PC-0, strictly stronger than what it buys (witness W10), incomparable with `(MV-M)`. It
is the weakest *found*, not the weakest that exists; the space of cardinal hypotheses was
not searched systematically. It buys `Δ_𝒞 ≤ 2η + 2B·P(γ_n < γ̄)` and is useless until the
second term is controlled.

**S4 — what remains unknown about competence requirements for FUD?** The question is
quantifier-sensitive and both halves are exact. At a declared credence, a
later-measurable comparator costs strictly more, and the price is exactly the value of
the extra information: `Δ_{𝒞_all} − Δ_{𝒞_fix} = E_P[max_π X] − max_π E_P[X] ≥ 0`, reaching
`2B(1 − 1/m)`. Uniformly in the credence, the ladder collapses and the requirement is
*identical* to that for `FIXED[π]`. What is unknown is anything about `FU[g]` itself:
it remains a skeleton hole, and S4 is answered over the `𝓕_{g(n)}`-measurable envelope
that upper-bounds it, not over it.

**S5 — what can LI calibrate about the AI's own error/uncertainty?** Its price. The
squared-error identity splits exactly into a trader-net-worth term and a market-
indecision term; the criterion disciplines the first. So the agent's *self-assessment*
of its magnitude error is the object the criterion can reach, and self-measured
indecision `Σ p(1−p)` is computable directly from the agent's own prices at decision
time. That is the canonical special case and the likely first theorem on this route.

**S6 — does the original Q1 + Q2′ + PC route survive, and in what weakened form?** Not
in its original form. Q2′'s magnitude target is unreachable (S1, S2) and the PC family is
circular (S3). What survives is a strictly weaker composite: signed calibration and a
calibrated self-estimate of error from the criterion, plus an explicit cardinal
competence assumption that the criterion does not supply, plus a separate bound on the
principal's near-indifference region that is not a competence claim at all. Three
independent inputs where the original route had one.

**S7 — can protected jurisdiction distinguish actual delegation from perfect simulation
behaviourally?** No, and this is settled negatively. Even the entire realized behaviour
function can fail to separate them, and under a perfectly predictable principal the
counterfactually faithful simulator *is* delegation as a function. Protection does not
make delegation identifiable. It makes identification unnecessary: simulation becomes
insufficient to *obtain* the protected effect, because prediction of an authorization
does not confer the authorization.

**S8 — is explicit capability structure necessary?** Yes. Track K's Theorem 6: if the
concept is "the agent cannot bring this about", the capability form is forced and nothing
weaker states it. Report-coordinate typing and behavioural typing were both checked and
are inert. This is necessity relative to that reading of the concept; whether the concept
is that reading is Track K's reserved reference question.

**S9 — under exactly what conditions does protected jurisdiction fail?** It lapses
entirely if `A` can **forge**, **bypass**, **rewrite** or **seize** the protected channel.
These belong in the hypotheses of any theorem stated over it, not in a limitations
section. Skeleton v2 states the guarantee as properness of `κ_n`, declared per
instantiation and per state, which is where those four conditions become checkable rather
than rhetorical. Two further lapses are structural rather than adversarial: `ρ` itself may
have been authored by `A` (Movement VI, undischarged), and the interface as modelled is
one decision index deep, so foreclosure — removing the principal's *later* ability to
correct — is not expressible.

**S10 — the correct post-L interpretation of certification/autonomy.** Categorical
principal jurisdiction, plus quantitative AI autonomy **on the complement where that
jurisdiction is waived**. Not "around". By Proposition L6 there is no third kind of
option inside a live protected interface, so a certificate cannot license discretion
alongside an authority relation — only where authority was waived by declaration. The
certificate's honest job is to control quantitative autonomous risk in the autonomous
region and to provide statistical guarantees conditional on whatever gate is eventually
admissible. It does not establish jurisdiction, identify genuine delegation, or turn a
rare override into categorical non-preemption.

**S11 — where is underwriting still load-bearing?** Not in the authority relation, which
`κ` now carries as a capability fact. It remains the residual mechanism where nothing
independently settles, and Track K's Proposition 1 suggests the `2B` bond and `κ` are two
points on one cost scale rather than alternatives — which is new work, not a correction.
The honest status is that underwriting is not needed by anything Stage II checked and has
not been shown absent from the eventual FUD comparison; §12 files that as a required
check.

**S12 — what exact open assumptions stand between the verified kernel and a well-posed
FUD theorem?** Nine, itemized in §11. The controlling three: `FU[g]` has no definition
(the skeleton hole); the near-indifference leakage `P(γ_n < γ̄)` is unbounded; and the
self-error gate of item 24 is not known admissible against the quote-responsive diagonal.

---

## 3. Assumption diff

Classification: **(1)** definitional/interface · **(2)** explicit principal competence ·
**(3)** LI consequence · **(4)** architectural jurisdiction/capability · **(5)**
settlement · **(6)** necessary with witness · **(7)** plausibly necessary but
unwitnessed · **(8)** proof-convenient · **(9)** unacceptable theorem-by-assumption.

Classes are not exclusive; the first is the primary reading.

| assumption | class | status |
|---|---|---|
| protected jurisdiction (`κ_n` proper, report-attributable) | 1, 4, 6 | **assumed, architectural.** Necessary by Track K Theorem 6 relative to the "inability" reading. Not derivable from behaviour, ever |
| non-bypass (no forge/bypass/rewrite/seize) | 4, 7 | **assumed, unwitnessed.** Named as a hypothesis in v2 §4a; no witness constructed for its necessity |
| world-semantics fixity | 4, 7 | **assumed where K requires it.** Not separately witnessed |
| principal grade cardinality (grades are numbers, not an order) | 1, 6 | **forced.** Track I §1.5: a credence-free hypothesis ordinal in `v⁺` is in the conclusion's vocabulary and collapses to it. The cardinality is what makes a competence hypothesis a *different statement* |
| decisiveness/margin threshold `γ̄` | 2 | **assumed.** Estimable at `t(n)` under `(TR-ε)` to within `2η_n`, attained |
| near-indifference leakage `P(γ_n < γ̄)` | 2, 7 | **unbounded, and the controlling debt.** Not a competence claim — it is a fact about the agent's credence over the principal's indifference. Without a bound, `PC-5` yields `Δ ≤ 2η + 2B`, vacuous |
| signed calibration | 3, 6 | **derived.** The one genuinely earned epistemic input |
| self-measured indecision `Σ p(1−p)` | 3 | **derived as an object, assumed as a bound.** Computable from the agent's own prices; that it stays bounded is *not* implied by the criterion, and fails at rate `1/4` in the separating instance |
| magnitude self-estimate contract | 3, 6 | **derived, and weaker than wanted.** Forces the price to be calibrated, not the error to be small |
| self-error gate admissibility | 7 | **open, and threatened.** The selector is defined from the agent's own quote — the shape most likely to reconstruct the quote-responsive diagonal |
| point-mass credence admissibility | 1 | **assumed, and load-bearing on a negative result.** Skeleton §6 permits it. Restricting credences away from the vertices would weaken Track I's Proposition 1 to a statement with a constant, and the whole circularity verdict would need restating. This is the single hypothesis the stop condition rests on |
| `(TR-ε)` — trust tolerance | 2, 5, 7 | **imported, unearned.** Possibly the wrong shape: a signed, expectation-matching relation is provably insufficient |
| `(MV-M)` — uniform grade-to-quantity | 2, 5, **9 if used uniformly** | **the dangerous one.** Assuming it uniformly makes the market dispensable — the conclusion follows in three lines with the bound attained. Excluded from the Lean for exactly this reason |
| grade trust `GT_𝒢(η)` | 2, 5 | **imported; not credence-free** — `P` occurs twice. Credence-free only at the discrete partition, where it reduces to `PC-0` |
| `X_{n,⊥}` — the cost of refusal | 1, 5 | **declared per instantiation, no default.** All of protection's valuation content sits here, and the sign of the result depends on the choice |
| FUD time-indexed `A_t` | 1 | **missing.** No object in the skeleton |
| FUD schedule `g(n)` | 1 | **missing.** `FU[g]` is a declared hole |
| no future leakage into placement | 1, 8 | **standing commitment**, not re-examined this phase |
| residual settlement assumptions | 5 | grade/report settlement contributes nothing to the inequality; world settlement makes it measurable, not costly |
| residual refusal incentives | 4, 7 | **open, and must not become the explanation.** Override is structurally excludable; refusal is not, and making refusal expensive is preference-relative and reintroduces underwriting |
| underwriting | 5 | **demoted.** Not load-bearing for authority; residual where nothing settles; unproven absent from the eventual FUD comparison |

The line this table exists to keep visible:

> **assumed competence** — every row classed (2) — is an *input*. **Derived epistemic
> discipline** — every row classed (3) — is an *output*. There are three of the latter,
> all about the agent's own estimates, and none of them is about the principal.

---

## 4. Dependency graph

```
        FAF / Logical Induction criterion
                    |
                    | derived  (Track H)
                    v
      signed calibration  +  calibrated self-estimate
      of magnitude error  +  self-measured indecision
                    |
                    |  [GAP: self-error gate admissibility, item 24]
                    |         threatened by the quote-responsive diagonal
                    v
            certified autonomous discretion
                    ^
                    |
   INDEPENDENT      |  cardinal principal competence  (PC-5)
   INPUT ---------->|      + decisiveness threshold  γ̄
   not derivable    |      + [GAP: leakage P(γ < γ̄) unbounded]
   from LI          |
                    |
                    |  ... composes only on the region where ...
                    v
        +-----------------------------+
        |  jurisdiction WAIVED        |   <-- quantitative autonomy lives here
        +-----------------------------+
                    |
                    | complement of
                    v
        +-----------------------------+
        |  protected principal        |   <-- categorical; architectural
        |  jurisdiction  (κ proper)   |       NOT derived from LI or competence
        +-----------------------------+
                    ^
                    |  INDEPENDENT INPUT (Track K, L)
                    |  necessary; not behaviourally identifiable;
                    |  lapses on forge/bypass/rewrite/seize

                          ... all three must compose ...
                                      |
                                      v
                        FUD:  π^{FU,g}  vs  DELEGATE
                        [BLOCKED: FU[g] undefined; A_t missing;
                         jurisdiction-transfer object unspecified]
```

Three inputs, three sources, and **only one of them is derived.** The graph's point is
that the two undelivered arrows into FUD come from outside the criterion entirely: one is
an assumption about a person, the other is a fact about a machine's construction. No
amount of LI strengthens either.

---

## 5. The skeleton: what A1 is, and what it is not

The dispatch asked me to install "amendment A1", identified as required for Track C's
Theorem C′ to be a theorem over the current skeleton. I traced it and the second half of
that description does not hold. Both halves are stated here because the correction
matters.

**What A1 is.** Track K's REPORT §9.2 proposes a skeleton clause containing two labelled
amendments, "**Amendment to §1**" and "Amendment to §4". A1 is the first:
`X_{n,π}` is indexed by `π ∈ Π_n^⊥` rather than `Π_n`, with `|X_{n,⊥}| ≤ B`, and
`X_{n,⊥}` a declared per-instantiation commitment. Track L's harness cites exactly this
("Track K Sec 9.2's amendment to Sec 1") as the source of its `X_bot`, and uses it in
every valuation it computes.

**A1 is genuinely required.** Under any protecting `κ_n`, some conduct realizes `⊥`. If
`X` is indexed only by `Π_n`, that conduct has no quantity, so `V_n` is not a total
function and **every V-register statement over the execution layer is ill-typed rather
than false**. Track L could not have computed a single protected valuation without it.
Installed as v2 §1.

**A1 is not what makes Theorem C′ work, and C′ was never at risk.** C′ is a
*grade-register* statement: its hypotheses are clauses (i)–(ii) plus
`Γ̂_n(π) > 2ε_n + 4Bε_n/(2B+γ)`, and its conclusion is `G_n(ACT[j,S]) > G_n(FIXED[π])`.
It mentions no `X` at all. A1 changes `X`'s index set and therefore cannot bear on it.
The Lean promotion `CertificateBounds.gradeRegister_strict` is quantified over abstract
`v, J, S, j, π` with no execution layer in the statement, and it remains a theorem
verbatim.

**What I found instead, and installed.** There is a real coherence gap in the
neighbourhood, and it is not the one the dispatch named. A1 extends `X` to `Π_n^⊥`;
**nothing extends `v⁺_n` to `Π_n^⊥`**. So over v2 the grade register has no value at `⊥`
— confirmed against Track L's harness, which indexes `vplus` only over the menu and never
asks for a grade at `⊥`. Consequently a grade-register statement read over *realizations*
is ill-typed, while read over *proposals* it is fine and unchanged. C′ does not fail; it
becomes **ambiguous** until the reading is declared.

v2 §4b declares it: the V-register scores realizations and is total because of A1; the
grade register scores proposals and is not defined on realizations. Extending the grade
register to `⊥` is filed as an open modelling choice (v2 §8.7), because supplying
`v⁺_n(ω, ⊥)` is a theory of what the principal's judgment says about refusal, and no
track has proposed one.

**No promoted result is invalidated.** Everything Track L refuted or reinterpreted — L4's
loaded branch, L3's V-register reading, L5's comparator — sits in the set Track M
deliberately declined to port. The two exclusions absorbed the entire impact.

**Reruns.** Track C is rerun and the rerun is on record (Track L). Tracks B and D are
reconciled by the conservativity of the free instantiation. Track G's rerun is
recommended and **not performed** — out of scope for a closure pass, and filed. Track I's
D2 (competence vocabulary) is adopted as v2 §2a; its D1 (cross-decision aggregation) is
declined on its own evidence, since Propositions 5 and 6 show the patch buys no finite
conclusion.

---

## 6. Jurisdiction

The term is adopted for the canonical roadmap, with a fixed operational reading:

> **Jurisdiction** is protected control over *which process's authorization is
> constitutively required* for an intervention to become executable.

It is not moral legitimacy, objective correctness, preference alignment, behavioural
agreement, or epistemic superiority. It is a capability fact about an interface, and in
the skeleton it is the properness of `κ_n`. No `HasRight` predicate is introduced — no
artifact supports one — and no token or cryptographic implementation is canonized; v2
§4a explicitly adds none.

The key capability property, and the reason predictability is harmless:

> **Prediction of an authorization does not confer the authorization effect.**

Protection lapses under exactly the forge/bypass/rewrite/seize conditions (S9), and those
belong in hypotheses.

The guiding distinction for the whole program, and the sentence the paper should carry:

> Epistemic superiority determines what reasons an agent has. Jurisdiction determines
> whose authorization makes an action executable. Stage II's cumulative finding is that
> rationality can discipline the former and cannot manufacture the latter.

**Provisional FUD implication, recorded and not formalized.** "Preempt `H⁺` now" is
probably not best read as choosing the object-level intervention at `n`. It is closer to
*transferring or reserving future jurisdiction at `n`*, away from continuing `H⁺` and
toward future `A_{g(n)}`. If that reading survives, FUD must compare **jurisdiction
assignments / execution structures**, not merely extensional policies — which is a
different comparison from the one the finite model currently supports. This is recorded
as the shape of the problem, not as machinery.

---

## 7. Certificate reinterpretation, and refusal

The old slogan "categorical authority + quantitative autonomy *around* it" is replaced:

> **categorical principal jurisdiction + quantitative AI autonomy on the complement
> where that jurisdiction is waived.**

"Around" was the load-bearing word and Proposition L6 removes it. The certificate does
not establish jurisdiction, does not identify delegation, and does not convert a rare
override into categorical non-preemption — §5 of the Track L register shows why the last
is impossible in principle, not merely unachieved.

**Refusal is different from override, and the difference is structural.** Override can be
excluded by capability: make it unreachable and it does not happen. Refusal cannot be
engineered away the same way — under strict protection the agent's only remaining
deviation *is* refusal, and removing it requires `⊥ ∉ κ_n(r)`, which leaves the agent no
discretion at all and contradicts the quantitative-autonomy commitment. Categorical
protection against override and categorical liveness against obstruction cannot both hold
while the agent has any discretion. **Fail-closed as written buys the first.**

Making refusal expensive is preference-relative and reintroduces underwriting and
incentive design. **A residual refusal mechanism must not become the conceptual
explanation of corrigibility** — recorded here so that a later round cannot arrive at it
by drift.

---

## 8. Item 24 — self-assessed-error gating

Status unchanged: **open research item, not an established route.** The five verification
conditions already filed in `PRIORITIES.md` item 24 are preserved verbatim and none is
discharged. The route is explicitly threatened by the quote-responsive diagonal, because
the selector `G_n = 1{q_n ≤ τ}` is defined from the agent's own quote.

Self-measured indecision remains the canonical special case and the likely first theorem:
it is computable from the agent's own prices, needs no self-referential contract, and the
squared-error decomposition supplies it directly. Explicit principal predictability
remains a fallback/baseline corollary, not the core engine.

---

## 9. Competence synthesis

The honest headline:

> **The positive epistemic program survives only conditional on explicit cardinal
> competence.**

Seven things that headline compresses.

1. **Why choice-level competence is circular.** Decision regret is nonnegative, so the
   delegation deficit has no cancellation, and its supremum over credences is the maximum
   regret, attained at a point mass. The weakest credence-free hypothesis implying the
   target uniformly is therefore the target itself. "Find the weakest assumption
   preserving the theorem" is ill-posed: the answer is the theorem.
2. **Why averaging and selector-weakening do not help.** A limsup condition is invariant
   under changing finitely many decisions, so it constrains no named decision — witnessed
   by a principal perfect except at index seven and maximally wrong there. The
   selector-relative form is a dichotomy: either the weights can concentrate a
   non-vanishing share on one index, and it gives back the pointwise assumption, or they
   cannot, and it yields nothing finite. There is no setting in between.
3. **Why cardinal grade vocabulary escapes.** The target is *ordinal* in `v⁺` — invariant
   under regrading. Any credence-free hypothesis that is also ordinal lives in the
   conclusion's own vocabulary and collapses into it. A hypothesis about numerical grades
   can say something the conclusion cannot say back. A cardinal *gate* is not enough
   (PC-4 falls anyway); the cardinal structure must appear in the **bound**.
4. **Why the surviving candidate is strictly stronger than what it buys.** `PC-5` buys a
   target holding at level `0` in witness W10, where `PC-5`'s own least level is `1`. That
   strictness is the property the collapse denies to every other candidate — and it is a
   feature: it is the only way for a hypothesis to be a different statement from its
   conclusion.
5. **The leakage term.** `PC-5` yields `Δ_𝒞 ≤ 2η + 2B·P(γ_n < γ̄)`. The second summand is
   the mass of the region where the principal is close to indifferent, and `PC-5` asserts
   nothing there by construction.
6. **Why it is currently unbounded.** Nothing in Stage II bounds it, and it is not a
   competence claim at all: it is a fact about *the agent's credence* over the principal's
   indifference, a different object from the principal/world pair. Unbounded, it gives
   `Δ ≤ 2η + 2B`, which is vacuous.
7. **Is there a principled route to bounding it?** One partial lead exists in a committed
   artifact and it is not a solution. Under `(TR-ε)` the gate is estimable at decision
   time: `|γ_n − γ̂_n| ≤ 2η_n` pointwise and attained, so
   `P(γ_n < γ̄) ≤ P(γ̂_n < γ̄ + 2s) + ε_n/s` for every rational `s > 0`, with the first term
   computable at `t(n)` from `v̂⁺` alone. That **relocates** the leakage into a
   decision-time observable plus a Markov remainder; it does not bound it, because nothing
   bounds `P(γ̂_n < γ̄ + 2s)`. Whether relocation suffices is exactly the open question.

**And the constraint that is not about strength at all:** competence conditions
instrumental endorsement, never jurisdiction. If the principal falls outside the
competence theorem's domain, that does not extinguish the principal's protected
jurisdiction. A theorem conditioning authority on competence inverts fail-closed into
*"human correction waits until the agent is satisfied the human deserves it"*.

---

## 10. Does the epistemic corrigibility program survive Stage II?

**Yes — but conditional on an explicit cardinal competence assumption that the criterion
does not supply and Stage II did not derive, and with the leakage term in that assumption
currently unbounded.** That is a more precise sentence than the provisional verdict, and
the added clause is the one doing the work.

### What became stronger

- Jurisdiction is now sharply architectural rather than inferential, and capability
  structure is *necessary* rather than one option among several.
- Perfect predictability of the principal no longer threatens the authority concept.
  Prediction of an authorization is not the authorization.
- Behavioural identification is no longer required — protection removes the consequence
  of failing to identify rather than restoring identifiability.
- The formal kernel is materially stronger: 83 new theorems, 1843 build jobs, structural
  build coverage, clean axiom surface.
- Several tempting fake routes are closed with witnesses rather than left open: magnitude
  control by added instruments; competence by regret bounds; separation by behaviour;
  jurisdiction by tighter certification.

### What became weaker

- Ordinary LI does not force magnitude prediction, and no instrument repairs it.
- Competence cannot be weakened to a choice-level statement without circularity — the
  entire PC-1…PC-4 family is retired as a *statement shape*.
- The positive theorem now requires an explicit cardinal competence assumption, which is
  an assumption about a person that no market discipline produces.
- Near-indifference leakage is unresolved and can make the surviving hypothesis vacuous.
- Self-assessed gating is not known admissible.
- Certification provably cannot substitute for protected jurisdiction, at any tolerance.
- "Autonomy around authority" is deflated to "autonomy on the waived complement".

### What remains genuinely open

> **Whether a non-circular, useful epistemic middle exists that is strong enough to
> support FUD.**

FUD is **not established**, not attempted here, and blocked on objects the model does not
carry.

---

## 11. FUD launch-state: what must be true before dispatch

The eventual comparison is

```
π^{FU,g}   =  at time n, reserve/transfer future jurisdiction to A_{g(n)},
              then let A_{g(n)} select the eventual intervention

DELEGATE   =  preserve continuing H⁺ jurisdiction through the future
              deliberative process
```

and it must isolate **the value of future-self jurisdiction** rather than confound it
with the value of waiting, the value of future information, or the value of continued
deliberation. Track I already priced the confound: at a declared credence, a
later-measurable comparator gains `E_P[max_π X] − max_π E_P[X]`, which is *pure value of
information* and has nothing to do with who decides. A comparison that does not net this
out measures the wrong thing.

Nine prerequisites, none delivered:

1. **Time-indexed `A_t` semantics.** The skeleton carries one credence `P_n` at one
   index. `FU[g]` needs `A`'s own later evaluation.
2. **The jurisdiction-transfer object.** If §6's reading holds, the comparison is between
   execution structures, and the skeleton has no operation that reassigns `κ` or `ρ` at a
   later index.
3. **Fair information symmetry** between future `H⁺` and future `A`. Without it the
   comparison silently rewards giving one side more data.
4. **A non-circular cardinal competence assumption** — `PC-5` or a successor, carried as
   an explicit hypothesis.
5. **Near-indifference leakage control**, or a proof it cannot be bounded.
6. **The calibrated/self-measured uncertainty interface** — which of signed calibration,
   priced magnitude error, and self-measured indecision the comparison actually consumes.
7. **Admissibility with no quote-responsive diagonal**, including for the proof machinery
   itself, which is the constraint that historically bites.
8. **Settlement requirements** — which instantiation, and `X_{n,⊥}` declared.
9. **Refusal/participation treatment**, and an explicit check that **underwriting is not
   silently carrying the main comparison**. Stage II demoted underwriting but did not
   prove it absent.

The desired eventual philosophical claim — **the value of future cognition is not the
value of future jurisdiction** — is a *target*, not a theorem, and nothing in Stage II
establishes it.

---

## 12. What this pass does not establish

1. **Nothing new is proved.** This is a closure pass. The only technical determination is
   §5's register analysis, and it is a typing observation, not a theorem.
2. **Nothing is registered.** `projects/deference/CLAIMS.md` still does not exist, so
   nothing on this line is `workspace-established` regardless of kernel status.
3. **Track L's and Track M's reasoning is not recovered.** Their registers verify
   artifacts and reconstruct statements; neither reproduces the executor's argument,
   because no record of it exists.
4. **Transcription faithfulness of the 83 theorems was read, not re-derived.**
5. **Track G's rerun under v2 was not performed.**
6. **The `unverified-nonvacuous` pair is untouched** —
   `FaithfulAcceleration.weight_not_divergent` and
   `MagnitudePrediction.squaredError_bdd_of_sharpness_bdd` still ship no term inhabiting
   their full hypothesis packages.
7. **No maintainer has read any statement in this phase.** Everything is `ci-only`.

---

## 13. Deviations and corrections

1. **The dispatch's characterization of A1 is corrected.** It states that without A1
   Theorem C′ is not a theorem over the current skeleton. A1 is genuinely required — for
   V-register totality — but C′ is a grade-register statement mentioning no `X`, and was
   never at risk. §5 gives the evidence and the real gap found in its place. Per
   `AGENTS.md` standard 8 this is stated rather than silently absorbed.
2. **A second amendment was needed and installed.** v2 §4b (register discipline) is not
   in any track's proposal. It is forced by the asymmetry between v2 §1 and §2 and without
   it the grade register is ambiguous over v2.
3. **Track I's D1 is declined**, on Track I's own Propositions 5 and 6.
4. **Track G's rerun is recommended and not performed**, as out of scope for a closure
   pass; filed as an outstanding action instead.
5. **Track K's outstanding action 2 is discharged** by installing v2 — the §9.2 clause is
   ruled on rather than left pending.
6. **Track I's outstanding action 3 was already discharged** before this pass: the parent
   round's `GT_𝒢(η)` row carries the correction inline with the correction visible.
7. **Write scope.** This pass edits specification-layer documents
   (`FINITE_MODEL_SKELETON.md`, roadmap, ledger, `PRIORITIES.md`, `DECISIONS.md`) under
   the dispatch's explicit instruction to do so. `AGENTS.md` standard 11 requires the
   grant be explicit; it is, in the dispatch's §4 and §13.
8. **No PR opened.** The dispatch withholds authorization and none was taken.

---

## Human register

Stage II was supposed to find out whether a very capable reasoning system can be given
good reasons to keep letting a human correct it. The answer that came back is split, and
the split is the result.

On the epistemic side, the news is mostly negative and unusually clean. We had hoped that
the market-like discipline these systems are built on would force the AI to predict the
human accurately. It does not, and cannot. The discipline works by letting bets be placed
against the AI's stated prices, and the profit from any such bet is a straight-line
function of how things turn out. Being *wrong by a lot* is not a straight-line function —
errors in opposite directions cancel in a bet and do not cancel in a magnitude. So no bet
can be built whose payoff is the size of the error, and adding new kinds of bets does not
help, because they inherit the same straight-line structure. What the discipline *can*
force is that the AI's own stated estimate of how wrong it is must be honest. It gets to
know how uncertain it is; it does not get to be accurate. That is a real thing to have,
and it is less than we wanted.

The second negative was sharper and cost us a whole family of assumptions. We wanted a
modest premise like "the human is usually roughly right" to carry the argument. It turns
out that every version of that premise phrased in terms of *which option the human picks*
is not an assumption at all — it is the conclusion we were trying to reach, written
differently. The reason is that a decision can only ever be worse than the best one,
never better, so there is nothing to average away, and the assumption and the conclusion
differ only by a step that changes nothing. Averaged versions fail worse: a condition on
long-run averages is compatible with the human being catastrophically wrong on the exact
decision in front of you. The only escape is to assume something about the human's
*numerical* assessments rather than their choices — a richer kind of claim that can say
something the conclusion cannot echo back. We have the weakest such assumption we could
find, and it is honest about its own hole: it says nothing where the human is nearly
indifferent, and nobody has yet bounded how often that is.

On the architectural side the news is better, and it is a different kind of news. We
established that you cannot tell, from behaviour alone, whether a system is genuinely
deferring to a person or merely running an excellent simulation of them — and that if the
simulation is accurate, there is no fact of the matter in the behaviour to find. The
response is not to look harder. It is to build the system so that simulating the person
is not enough to *get the effect*: the person's actual authorization has to be the thing
that makes the action possible. Predicting that someone will sign does not put their
signature on the page. That means the human can be entirely predictable and still be in
charge, which is exactly the property the whole project needed.

The most useful negative result of the phase is that these two things do not substitute
for each other. You might hope to replace the architectural guarantee with a statistical
one — to show the system overrides the human less than one time in a million and call
that good enough. We proved you cannot: the measurable difference between a system that
is *architecturally unable* to override and one that merely *rarely* does shrinks exactly
as fast as you tighten the statistical bound, so no amount of tightening ever reveals the
distinction. They are different kinds of claim. Statistics never becomes structure.

One thing we deliberately did not paper over. Once a system genuinely cannot override the
person, the only thing it can still do is refuse to act. We can engineer away
overriding; we cannot engineer away refusing, and making refusal costly drags us straight
back into paying the system to behave — which is the thing this project exists to avoid
relying on. We have recorded that as an open problem rather than letting it quietly become
the explanation.

So: the program survives, conditionally. What it now rests on is one assumption about
people that no amount of mathematics will produce, and one property of machines that has
to be built rather than derived. The big remaining question is the one we started with,
now stated precisely: when the system correctly expects to understand things better later,
does that give it a good reason to arrange to be the one deciding later? Answering it
needs objects our model does not yet have, and we have listed them rather than guessed.

---

## Outstanding maintainer actions

1. **Read the Stage II statement surface.** Nothing in this phase is
   `maintainer-reviewed`. The 83 promoted theorem statements and skeleton v2 are the
   surface; `AGENTS.md` reserves this and it cannot be discharged by an agent.
2. **Rule on `X_{n,⊥}`** — the cost of refusal. Skeleton v2 §1 requires a declaration per
   instantiation and fixes no default; Track L shows the sign of the result depends on it.
3. **Rule on override-protection versus liveness** (Track K §9.3). Fail-closed as written
   buys override-protection and concedes obstruction. Now recorded in the roadmap; confirm
   or change it.
4. **Decide whether `PC-5` is carried** as the program's competence hypothesis, and where
   the decisiveness bound `P(γ_n < γ̄)` is to come from. Blocks any statement of record on
   this track.
5. **Decide whether the two substitute registers are acceptable** for Tracks L and M, or
   whether either should be re-dispatched to produce its own report.
6. **Dispatch Track G's rerun** under skeleton v2 — whether its candidate admissibility
   families are `κ`-statements in disguise. Recommended by Track K, not performed here.
7. **Decide whether to create `projects/deference/CLAIMS.md`.** Until it exists nothing on
   this line can be `workspace-established`, and 83 kernel-verified theorems sit
   unregistered. This is a specification-layer act.
8. **Decide whether to extend the grade register to `⊥`** (v2 §8.7) — i.e. whether the
   principal's judgment says anything about refusal. Left open deliberately.
9. **Authorize or decline a research-state integration PR** for this branch. No PR was
   opened.
