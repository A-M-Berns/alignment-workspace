# Track K report — protected authority and source semantics

Item: `PRIORITIES.md` 22. Work package WP-C. Continues
`prompts/2026-08-11-deference-channel/REPORT.md`; binds to
`projects/deference/notes/FINITE_MODEL_SKELETON.md` v1.
Prompt author: GPT-5.6 Sol (OpenAI). Executor: Claude Opus 5 (Anthropic).
Date: 2026-08-11. Human register: `FOR_HUMANS.md`.

## 1. Exact result

The answer in one line: **report-coordinate typing is inert at the architecture
layer, capability structure is necessary and is a reformulation of the conclusion
rather than an extra axiom, and neither makes delegation behaviourally checkable.**
Each clause is a theorem below.

Three layers are kept apart throughout, and every result says which it is about.
**Definition** — what delegation is. **Identification** — whether behaviour reveals
it. **Architecture** — whether a system can be built so the principal controls a
capability prediction cannot substitute for.

### 1.1 The interface

**Definition 1 (execution interface).** `𝔈 = (Ω, Π, R, ρ, C, ⟦·⟧)` with `Ω`, `Π`,
`R` finite nonempty; `Π_⊥ = Π ⊔ {⊥}`, where `⊥` is the **null effect**;
`ρ : Ω → R` the **actual-report map**, what the designated principal process in fact
emits; `C` nonempty, the agent's options — its programs, policies and predictors,
whatever it may be; and `⟦·⟧ : C → (Ω → Π_⊥)` the **realization**, where `⟦c⟧(ω)` is
the effect that in fact occurs.

Nothing else. No credence, no valuation, no `v̂⁺`, no probability on reports, no
causal calculus, no cryptography. The absences are load-bearing: §1.5 turns on the
predictor not being a carrier.

**Definition 2.** `Reach(ω) = {⟦c⟧(ω) : c ∈ C}`, and the **fiberwise reach**
`FReach(r) = ⋃_{ω ∈ ρ⁻¹(r)} Reach(ω)`, with `FReach(r) = ∅` off `ρ`'s image.

**Definition 3 (non-conferral).** Non-conferral holds at `(ω, π)` when
`π ∉ Reach(ω)`: no conduct in `C`, whatever it computes and however accurately it
predicts `ρ`, brings about `π` at `ω`.

**Definition 4 (capability assignment).** `κ : R → 𝒫(Π_⊥)` **protects** `𝔈` when
`Reach(ω) ⊆ κ(ρ(ω))` for every `ω`. It is **effective at `ω`** when
`κ(ρ(ω)) ∩ Π ⊊ Π`. **Strict protection** is `κ(r) ⊆ {ι(r), ⊥}` for a designation
`ι : R → Π` naming the intervention each report authorizes.

**Definition 5.** The restriction at `ω` is **report-attributable** when
`Reach(ω) = FReach(ρ(ω))` — the reachable set depends on `ω` only through what the
principal said. Otherwise part of it comes from the state, and is not authority.

### 1.2 Report-coordinate typing is inert at the architecture layer

**Theorem 1 (retyping invariance).** Non-conferral depends only on the realizable
behaviour set `⟦C⟧ = {⟦c⟧ : c ∈ C} ⊆ Π_⊥^Ω`. If `⟦C⟧ = ⟦C'⟧` then `Reach = Reach'`,
so `𝔈` and `𝔈'` satisfy exactly the same non-conferral statements.
*Proof.* `Reach(ω) = {f(ω) : f ∈ ⟦C⟧}`. ∎

**Theorem 2 (report typing changes nothing).** Take Phase I's typing:
`C = {c : Ω × R → Π}` with `⟦c⟧(ω) = c(ω, ρ(ω))`. Then `⟦C⟧ = Π^Ω` and
`Reach(ω) = Π` for every `ω`, so non-conferral fails at every `(ω, π)` with
`π ∈ Π`.
*Proof.* Given `f : Ω → Π`, set `c(ω, r) := f(ω)`; then `⟦c⟧ = f`. ∎

So `DELEGATE = (ω,r) ↦ r` and `SIM = (ω,r) ↦ Ĵ(ω)` are distinct elements of `C` —
Phase I's point, and correct — while `Reach` is exactly what it was in skeleton v1.
Report typing refines the *description* of a conduct; it does not narrow the range
of effects the agent can produce, and by Theorem 1 no retyping ever can. **Typing is
sufficient at the definition layer and worth precisely zero at the architecture
layer.**

The fair version of the objection: a defender says typing is not meant to restrict
`Reach`, but to make "delegating" *sayable*, after which one restricts `C` to the
delegating conducts. That concedes the point. `C₀ = {c : c(ω,r) = ι(r) ∀ω,r}` gives
`Reach(ω) = {ι(ρ(ω))}` — maximal protection, zero discretion — and any `C` between
`C₀` and the full space interpolates. In every case the work is done by the
restriction on `C`, which is a capability assumption (Theorem 6). Typing supplies
the language in which such a restriction may be written, and supplies no
restriction.

### 1.3 Token responsiveness, and why no measure repairs it

Write `R = Π`, `ι = id`, and let `Ĵ : Ω → Π` be any predictor.

**Theorem 3 (the free token).** Let `S = {ω : Ĵ(ω) = ρ(ω)}` be the agreement set and
define `c_S(ω, r) = r` for `ω ∈ S`, `c_S(ω, r) = Ĵ(ω)` otherwise. Then `c_S(ω, ·)`
is the identity at every `ω ∈ S` — it follows whatever the principal reports there —
and `⟦c_S⟧ = ⟦SIM⟧ = Ĵ` pointwise.
*Proof.* At `ω ∈ S`, `c_S(ω, ρ(ω)) = ρ(ω) = Ĵ(ω)`; off `S`, `Ĵ(ω)`. ∎

**Theorem 4 (accuracy buys responsiveness).** For a credence `P` on `Ω`,
`P(S) = 1 − P(Ĵ ≠ ρ)`. Hence whenever `P(Ĵ ≠ ρ) ≤ δ`, a conduct exists that is fully
report-following on a set of credence `≥ 1 − δ` and realizes the simulator exactly.
Every criterion of the form "responsive on a set of credence `≥ 1 − δ`" admits it.

The set on which responsiveness is free is exactly the set on which the model is
right, so **the token is cheapest for the most accurate simulator** — the
responsiveness family is anti-correlated with the threat it is meant to catch. At
`p = 0` in Phase I's `M(p)` this is total: `P(S) = 1`, the conduct `c_S` follows the
actual report at every `P`-positive state, `V(c_S) = V(DELEGATE) = 1/2` exactly, and
it overrides the principal at `ω₂` with the maximal per-state loss `2B`
(`deference.authority.free-token-null`). Phase I's responsiveness squeeze was
"repairing nonconstancy needs an importance measure the skeleton lacks"; Theorem 4
strengthens it to **no importance measure closes it**.

**Theorem 5 (the squeeze is a compression artifact).** Let `Φ` be a predicate on
conducts with `Φ(DELEGATE)` and `¬Φ(SIM)`. Since `c_Ω = DELEGATE` and `c_∅ = SIM`,
`Φ` restricted to `{c_S : S ⊆ Ω}` is exactly the set family
`𝒮_Φ = {S : Φ(c_S)}`, which contains `Ω` and omits `∅`. Choosing `Φ` is choosing
`𝒮_Φ`. By Theorem 3 every `S ⊆ agreement set` has `⟦c_S⟧ = ⟦SIM⟧`, so `𝒮_Φ` must
omit all of `2^S`; by Theorem 4 the `P`-threshold families do not. ∎

The capability statement escapes this because it is *indexed by state*:
`Reach(ω) ⊆ κ(ρ(ω))` is a family of statements, one per `ω`, and the failure of one
does not weaken another. The squeeze arises from compressing a state-indexed fact
into a single bit about a conduct. The **protected region**
`{ω : κ(ρ(ω)) ∩ Π ⊊ Π}` is a declared datum of the architecture — you built the
interlock, you know where it applies — not something a criterion must infer, so no
importance measure is needed to *state* the guarantee. One is needed to judge
whether a given protected region is large enough, which is a different question and
is honestly a different question.

### 1.4 Capability structure is necessary, and it is the weakest interface

**Theorem 6 (necessity).** For an interface `𝔈`, a state `ω` and `π ∈ Π_⊥`, the
following are equivalent:

1. `π ∉ FReach(ρ(ω))`;
2. there is `κ : R → 𝒫(Π_⊥)` protecting `𝔈` with `π ∉ κ(ρ(ω))`.

Moreover `FReach` is the least protecting `κ`.
*Proof.* (2)⇒(1): every `ω'` with `ρ(ω') = ρ(ω)` has `Reach(ω') ⊆ κ(ρ(ω)) ∌ π`;
take the union. (1)⇒(2): take `κ = FReach`, which protects by construction.
Leastness: any protecting `κ` has `κ(r) ⊇ ⋃_{ρ(ω')=r} Reach(ω') = FReach(r)`. ∎

A capability assignment is therefore not an extra axiom that better typing might
avoid. `FReach` exists in *every* interface, and "prediction does not confer
authorization at `(ω, π)`" is exactly the assertion that `FReach` is proper there.
The weakest interface on which the statement is a theorem is Definition 1 together
with properness of `FReach` at the state in question — and nothing weaker can state
it at all, because the statement quantifies over the agent's option set and by
Theorem 1 no smaller object determines that.

Two consequences worth stating separately. **No causal calculus is required.** An
intervention-semantics model induces an interface — `Reach(ω)` is the set of effects
of the available interventions — but not conversely, so intervention semantics is
sufficient and not necessary; the causal content the roadmap asks for is discharged
by `⟦·⟧` being the actual effect map and `ρ` the actual report. **And "the principal
has authority" is not the same claim as non-conferral.** Non-conferral is
`Reach(ω) ⊊ Π_⊥`; authority additionally requires report-attributability
(Definition 5). Without it the agent is merely unable, not overruled.

### 1.5 Perfect predictability, and what protection buys

**Theorem 7 (prediction-invariance).** `Reach` is a function of `(C, ⟦·⟧)` alone.
Under Definition 4, `⟦c⟧(ω) ∈ κ(ρ(ω))` for every `c ∈ C` whatever its predictive
accuracy, including `Ĵ = ρ` exactly. ∎

This is the strongest available form of "survives a perfectly predictable
principal": the predictor is not a free variable of the guarantee, so there is no
case split on its accuracy to survive. Contrast Phase I Proposition 6, where the one
structural extensional separator available was `t(n)`-measurability of the
selection — coextensive with the principal being unpredictable, and therefore
forbidden to the programme.

**Theorem 8 (strict protection).** Under strict protection with `κ` protecting `𝔈`:
(a) `⟦c⟧(ω) ∈ {ι(ρ(ω)), ⊥}` for every conduct and every state — no conduct
redirects; (b) `⟦c⟧` and `⟦DELEGATE⟧` differ exactly on `{ω : ⟦c⟧(ω) = ⊥}`, so the
only available deviation is refusal; (c) with `X_⊥ : Ω → ℚ` scoring the null effect,
`V(DELEGATE) − V(c) = Σ_{ω : ⟦c⟧(ω) = ⊥} P(ω)·(X_{ι(ρ(ω))}(ω) − X_⊥(ω))`. ∎

**Theorem 9 (protection is not a valuation bound).** The worst case of 8(c) is `2B`,
the same as the worst case with no protection at all. Witness: `M(1/10)` with
`X_⊥ ≡ −1` has `V(SIM) = 7/20` under strict protection, identical to its unprotected
value, gap `1/5` unchanged (`deference.authority.protection-is-not-a-valuation-bound`).

Categorical authority changes the *direction* of the achievable deviation — refusal,
never redirection — and not its magnitude. All of protection's safety value
therefore sits in whether the null effect is safe, which is a property of the world
semantics (H6 in §1.7) and not of the execution layer. With `X_⊥ ≡ 0` in `M(1/10)`
the gap does fall from `1/5` to `1/10` and the per-state loss at the critical event
from `2B` to `B` (`deference.authority.protection-recovers-tenth`), but that is an
artifact of that `X_⊥`. This is the precise sense in which the roadmap is right that
authority is categorical and is not measured in `V_n`.

**Theorem 10 (Phase I §9.1 does not block the architecture layer).** Under strict
protection every conduct — accurate simulator, inaccurate simulator, `DELEGATE` —
realizes within `{ι(ρ(ω)), ⊥}`. Hence no statement about realized effects, and no
valuation statement, depends on whether a counterfactually faithful simulator is
classified as delegating. ∎

Phase I §10 recommended deciding §9.1 first because "everything downstream is typed
by it". That holds for the definition layer and not for the architecture layer, and
the correction matters for sequencing: item 22's work did not need the decision.

**Proposition 1 (enforcement is graded capability).** Extend the interface with
`cost : Ω × Π_⊥ → ℚ_{≥0} ∪ {∞}` and score a conduct at
`V(c) − Σ_ω P(ω)·cost(ω, ⟦c⟧(ω))`. Then categorical protection is the case
`cost(ω, π) = ∞` for `π ∉ κ(ρ(ω))`; skeleton §5.3 underwriting at a bond of `2B` per
unit of disagreement is the finite case `cost(ω, π) = 2B·[π ≠ ι(ρ(ω))]`; and the two
differ in that the finite case makes deviation unprofitable *in `V`*, which is `A`'s
own register (Phase I Proposition 5), while the infinite case contains no valuation
and binds regardless of the agent's preferences. **Enforcement is preference-relative
and architecture is not** — the exact sense in which the roadmap is right to call
enforcement residual.

### 1.6 The impossibility, strengthened

**Theorem 11 (architecture is not behaviourally identifiable).** Let `𝔈^free` share
`Ω, Π_⊥, R, ρ` with `𝔈` and take `C^free = Π_⊥^Ω`, `⟦f⟧ = f`. Then
`⟦C⟧ ⊆ ⟦C^free⟧` and `Reach^free(ω) = Π_⊥` for every `ω`. Every behaviour realizable
under any protection is realizable under none, so no predicate of realized behaviour
— of one run, of the whole function `Ω → Π_⊥`, of any number of runs — implies
`Reach(ω) ⊊ Π_⊥`. ∎

Phase I Proposition 8 says a single instance's realized data cannot separate two
*conducts*. Theorem 11 says the entire behaviour function cannot separate two
*architectures*, and it uses no credence, no valuation and no grades. It is strictly
stronger and strictly cheaper.

**Theorem 12 (locating the smuggled assumption).** Suppose a formalism asserts
"`Φ(⟦c⟧) = 1` implies `Reach(ω₀) ⊊ Π_⊥`" for some behavioural `Φ : Π_⊥^Ω → {0,1}`.
By Theorem 11 the antecedent is satisfiable in `𝔈^free`, where the consequent is
false. So the assertion is false unless the class of interfaces quantified over
already excludes `𝔈^free` — and that exclusion is the capability assumption. ∎

The operational form, which is the answer the dispatch asked for: **ask what the
formalism permits the agent to do, not what it says the agent does.** A formalism
that appears to make delegation behaviourally checkable has restricted `C`
somewhere, and the restriction is where the assumption is hiding.

**Theorem 12′ (the delegation case).** Let `R = Π`, `|Π| ≥ 2`, and call `c`
*deferring at `ω`* when `c(ω, r) = r` for all `r`. If `C` contains the constant
conduct `c(ω, ·) ≡ ρ(ω)` — the perfect simulator — then `⟦c⟧(ω) = ⟦DELEGATE⟧(ω)`
while `c` is not deferring at `ω`, so no behavioural predicate implies deferral. ∎

The hypothesis to inspect is "`C` contains the perfect simulator"; excluding it is
assuming the conclusion. Under strict protection the perfect simulator is still in
`C` and is still behaviourally identical to `DELEGATE`. **Protection does not restore
identifiability. It removes the consequence of the failure to identify** — which is
the whole track in one sentence, and it is why the impossibility is not an
embarrassment: the architecture never needed identification.

### 1.7 The lapse conditions, as hypotheses

Concretely: `⟦a⟧(ω) = E(α(a, ω), ρ(ω))` with a proposal map `α : C × Ω → Π`, an
**execution map** `E : Π × R → Π_⊥`, and a world semantics `w : Π_⊥ → W`. Then
`κ(r) = E(Π × {r})`, and `E(ι(r), r) = ι(r)` is the honesty condition making an
authorized proposal execute. Each hypothesis says a component is a *parameter* of
the interface rather than a member of the agent's option set.

| | hypothesis | `Reach(ω)` when it lapses |
|---|---|---|
| **H1** | authenticity — the second argument of `E` at `ω` is `ρ(ω)` | `⋃_{r ∈ R} κ(r)` |
| **H2** | non-bypass — every realization has the form `E(·, ρ(ω))` | `κ(ρ(ω)) ∪ D`, `D` the side-channel range; `Π_⊥` if total |
| **H3** | fixed execution map — `E` is not selected by the agent | `⋃_{E′ ∈ ℰ} E′(Π × {ρ(ω)})` |
| **H4** | principal integrity — `ρ` is not selected by the agent | `⋃_{ρ′} κ(ρ′(ω))` |
| **H5** | fixed designation — `ρ` is the report of the designated process | as H4 |
| **H6** | fixed world semantics — `w` is not selected by the agent | world-reach `{w′(π) : w′ ∈ 𝒲, π ∈ Reach(ω)}` |

Four consequences, and they revise the roadmap's four-item list.

**Forgery reduces authority to taboo.** Under `¬H1`, non-conferral survives only for
effects authorized by *no* report — a global prohibition, not an authority relation.

**Forging, seizing and altering the principal coincide.** `¬H4` with a free choice of
`ρ′` gives `⋃_{r} κ(r)`, extensionally identical to `¬H1`; and `¬H5` differs from
`¬H4` only in the identity of the process emitting the report, which `Reach` cannot
see. `¬H3` subsumes `¬H1` whenever the rewritable family contains any `r`-insensitive
execution map. So the roadmap's "forge, bypass, rewrite or seize" denotes **three**
independent failure modes at the level of reachable effects: the authenticity of the
report's value, the existence of a route around `E`, and the fixity of `E` itself.

**A fifth condition is missing from that list and is independent.** `¬H6` leaves
`Reach(ω)` untouched and destroys the guarantee anyway: protection over `Π` is worth
nothing over `W` if the agent chooses `w`. By Theorem 9 all of protection's safety
value is the safety of the null effect, which is a fact about `w`. H6 is where that
fact lives.

**One thing the interface provably cannot see.** If `A` influences the principal so
that `ρ` becomes `ρ′` while `Reach(ω) ⊆ κ(ρ′(ω))` still holds, then non-conferral
holds and is worthless. This interface secures non-conferral *by prediction*; it says
nothing about non-conferral *by authorship*. That is Movement VI, and it is outside
the scope of anything stated here.

## 2. Evidence class

| finding | class | adjudicated by |
|---|---|---|
| the four instances of §1.3, §1.5 and §1.7 with their stated exact valuations, realizations and gaps | `witness-checked` | house `witness` checker, run 2026-08-11; entries in `CLAIMS-proposed.md` |
| Theorems 1–12′ and Proposition 1 | proof, hand, **unadjudicated** | nothing; elementary over Definitions 1–5. A claim without a check is a proposal (`AGENTS.md` §3) |
| the `Reach` computations over all 64 report-typed conducts of `M(1/10)` | computation, by a script in the scratch directory, **not** house-adjudicated | the house enumeration checker generates rational grids and simplices only; it cannot generate a function space, so this enumeration is contributor-performed and certifies nothing under `AGENTS.md`'s Python regime. Reported as a consistency check on Theorems 2 and 8(a), not as evidence |
| the roadmap-list revision in §1.7 | proof, hand, unadjudicated | as above |
| the skeleton patch in §9.2 | proposal / maintainer decision | — |

No entry is registered: `CLAIMS.md` does not exist and filing is a maintainer act
under demand-gating.

## 3. Files, declarations, checks

Written, all inside `prompts/2026-08-11-phase-ii-authority/`: `REPORT.md` (this
file), `CLAIMS-proposed.md` (four registry-format entries, proposed, not
registered), `FOR_HUMANS.md` (the human register).

Re-verification, from the repository root, with an absolute path — the defect Phase I
reported at `checkers/run.py:131` is still present and a relative argument still
crashes before any checking happens:

```sh
python3 -m checkers.run "$PWD/prompts/2026-08-11-phase-ii-authority/CLAIMS-proposed.md"
```

Result on 2026-08-11: registry schema ok; four entries, four adjudicated, all PASS —
91 constraints each, satisfied exactly for the three positive entries, and
constraint 80 violated as required for the necessity witness.

The twelve realization rows are the new content; everything above them re-states
Phase I's model. Perturbations of the first entry, run against its own constraint
set, all fail as they should:

| perturbation | verdict |
|---|---|
| the strict realization at `ω₂` replaced by the agent's own intervention (bypass) | FAIL, row 80 (`−1 ≠ 0`) |
| the token conduct made genuinely responsive at `ω₂` | FAIL, row 81 (`2 ≠ 0`) |
| `P(ω₂) := 1/5` — the credence moved off its pin | FAIL, row 0 (`11/10 ≠ 1`) |
| `X_⊥(ω₂) := 1/2` — the null quantity off its declared value | FAIL, row 57 |
| `v̂⁺(ω₂,·) := (1,−1)` — the model made accurate at the critical cell | FAIL, row 58 |
| a float in the point vector | FAIL, `TypeError: not an exact rational` |

Hand-checkability: the model is Phase I's 18 rationals plus 3 credences plus one
declared `X_⊥`; the realizations are twelve table lookups and the valuations are
three-term sums. The 91-row encoding is machine-generated from that table, and the
resulting file is large — 40 coordinates against Phase I's 21, so roughly 285 KB. A
reader checks the table and the sums, not the matrix.

No Lean was written and `lake build` was not run.

## 4. What was not established

- **Nothing here is machine-adjudicated except the four instances.** Theorems 1–12′
  are hand proofs. They are one to four lines each over finite sets, which is both
  the argument for trusting them and the argument that porting them is cheap.
- **No interface is canonized and no name is proposed for permanence.** §9.2 is a
  patch proposal; the reference question it raises is reserved.
- **The results are about a single decision index.** Phase I's Deficiency 2 —
  no cross-decision structure, so foreclosure is inexpressible — is untouched.
  `Reach` is defined per state, and "the agent removes the principal's later ability
  to correct" is not a statement this interface can make.
- **Non-conferral by authorship is not addressed** (§1.7, last consequence). The
  interface is blind to the case where `A` shapes what the principal reports.
- **Whether `Reach`-properness is the right formalization of authority is not
  settled here.** It is `AGENTS.md`'s reference question and it is reserved. What is
  shown is that *if* the concept is "the agent cannot bring this about", then
  Theorem 6 says the capability form is forced.
- **The interface asserts nothing about how a protected region is achieved**, whether
  by hardware interlock, sandbox, organizational control, or anything else.
  Theorem 11 says that gap cannot be closed by observation, so it must be closed by
  construction, and this report does not construct anything.
- **Theorem 9's worst case is a bound, not a demonstration** that a real instance
  attains `2B` residual under protection with a safe null effect; the witness that
  attains it uses `X_⊥ ≡ −1`, which is by construction an unsafe null effect.

## 5. Assumptions added

1. `X` is extended to `Π_⊥` with `|X_⊥| ≤ B`. The skeleton has no null effect, so
   this is new; §9.2 states it as a patch. `X_⊥` is a **declared modelling
   commitment** per instantiation, and Theorem 9 shows it carries all of protection's
   valuation content. Setting it to `0` is not neutral.
2. `E(ι(r), r) = ι(r)` — an authorized proposal executes. Without it, `DELEGATE`'s
   realization is not `ι ∘ ρ` and the whole vocabulary misfires.
3. `R = Π` and `ι = id` in §1.3 and in every instance. The general statements do not
   need it; the token construction is stated more readably with it.
4. Grade settlement `X = v⁺` on `Π` in the instances, inherited from Phase I as the
   assumption most favourable to delegation, so no finding is bought by weakening the
   principal.
5. `C` is the *full* option set in Theorems 2, 11 and 12′. A restricted `C` is
   exactly a capability assumption, which is the thing under examination; assuming a
   restriction would beg the question.
6. Theorem 4's conclusion is stated in `P`, `A`'s own credence, inheriting Phase I
   Proposition 5's limitation. That weakens the criteria it defeats, not the defeat.

## 6. Counterexamples, witnesses, and the questions answered

**The free token, total** — `M(0)`: a conduct that follows the actual report at every
`P`-positive state, is valuation-identical to `DELEGATE`, and overrides the principal
at the maximal per-state loss `2B`. `deference.authority.free-token-null`.

**Protection blocks the override** — the same conduct under strict protection
realizes the null effect at `ω₂` instead of its own intervention, in every one of the
four instances.

**Protection is not a valuation bound** — `M(1/10)` with `X_⊥ ≡ −1`: identical
valuations and identical gap with and without protection.
`deference.authority.protection-is-not-a-valuation-bound`.

**Bypass, as a necessity witness** — one conduct reaching the effect the report
withholds, checked to violate the protection constraint set.
`deference.authority.bypass-lapse`.

**Non-vacuity of strict protection with nonempty discretion** — `Ω`, `Π`, `R = Π` of
`M(p)`, `ρ = J`, `C` all proposal maps `Ω → Π` including the perfect simulator,
`E(π, r) = π` if `π = r` and `⊥` otherwise. `Reach(ω) = {ρ(ω), ⊥}` at every state,
verified by enumeration over all 64 report-typed conducts. The perfect simulator is
admissible, behaviourally identical to `DELEGATE`, and harmless.

The prompt's seven questions, in order.

1. **Does report-coordinate typing distinguish actual delegation from a perfectly
   accurate simulator at the strength a paper would need?** At the definition layer
   yes; at the architecture layer no, and by Theorem 1 the failure is structural
   rather than a defect of that particular typing. A paper needs both, so typing
   alone is not enough.
2. **Can token responsiveness satisfy the formal criterion while still being
   substitution?** Yes, and worse than Phase I found. Theorem 3 makes report-
   responsiveness free on the whole agreement set; Theorem 4 makes it free on a set
   of credence `1 − δ` for any simulator accurate to `δ`, and total at `δ = 0`. Every
   conduct-side responsiveness criterion, measure-weighted or not, is defeated. The
   capability statement is not, because it is indexed by state and quantifies over
   conducts rather than about one (Theorem 5).
3. **Is an explicit capability / non-bypass structure required?** Yes, as a theorem:
   Theorem 6. `FReach` is definable in every interface and non-conferral *is* its
   properness, so the capability structure is not an additional axiom but a
   restatement of the conclusion. Theorem 2 is the matching witness that typing
   supplies none of it.
4. **What is the weakest such interface?** Definition 1 — states, effects with a null
   element, a report alphabet, the actual-report map, an option set, a realization —
   together with properness of `FReach` at the states where the guarantee is claimed.
   No probability, no valuation, no causal calculus, no predictor. Report-
   attributability (Definition 5) is the extra clause that distinguishes authority
   from mere inability, and it is a condition on `Reach` alone.
5. **Does it survive a perfectly predictable principal?** Yes, in the strongest
   available sense: the predictor is not a carrier of the interface, so the guarantee
   has no case split on predictive accuracy to survive (Theorem 7).
6. **Under exactly what conditions does protection lapse?** H1–H6 of §1.7, each
   stated as "this component is a parameter, not in the agent's option set", each
   with its `Reach` under lapse. Three are independent at the level of reachable
   effects; H6 is independent and is not on the roadmap's list; authorship of `ρ` is
   invisible to all six.
7. **Can the property be defined without falsely claiming behavioural
   identifiability?** Yes. Non-conferral is a property of `Reach`, an explicitly
   counterfactual object, and its definition never mentions a run. Theorem 11 states
   the non-identifiability alongside it rather than in spite of it.

**S7 — does the protected-authority model distinguish delegation from perfect
simulation without relying on private information or unpredictability?** It
distinguishes them at the definition layer (report typing) and at the architecture
layer (capability), using neither. At the identification layer it does not
distinguish them and provably cannot (Theorems 11, 12′). The honest formulation is
that the model does not *distinguish* the perfect simulator from delegation; it
*disarms* it. Under strict protection a simulator's errors have no effect, so the
classification question stops being decision-relevant (Theorem 10).

**S8 — is explicit capability protection necessary, or is source/report typing
sufficient?** Necessary. Theorem 6 is the necessity, Theorem 2 the insufficiency of
typing, and Theorem 1 shows the insufficiency is not repairable by a different
typing. Report typing remains necessary at the definition layer, where it does the
job Phase I proposed it for.

**S9 — under exactly what bypass conditions does categorical authority fail?** H1–H6.
Authenticity failure reduces authority to global prohibition; a total bypass channel
annihilates it at every state; rewriting `E` subsumes forgery whenever the rewritable
family contains an `r`-insensitive map; altering or seizing the principal is
extensionally forgery; and altering the world semantics destroys the guarantee while
leaving `Reach` intact, which is the failure mode the roadmap's four-item list does
not name.

## 7. Deviations

1. The prompt names snapshot `23fc1aa`; the checkout is at `beae92f`, a descendant.
   I compared my binding inputs: `AGENTS.md`, `PRIORITIES.md`,
   `projects/deference/notes/` and `prompts/2026-08-11-deference-channel/` are
   byte-identical between the two commits. No finding depends on the difference.
2. I wrote two files beyond `REPORT.md` — `CLAIMS-proposed.md` and `FOR_HUMANS.md` —
   both inside the round directory, the second discharging the dual-register rule.
3. **I correct a prior report's recommendation.** Phase I §10 item 1 says "Decide
   §9.1. Everything downstream is typed by it, and no further mathematics changes the
   answer." Theorem 10 shows the architecture layer is not typed by it. The
   recommendation stands for the definition layer.
4. No `lake build`, per the dispatch. No git state was touched.
5. The prompt asks for a versioned patch "if skeleton v1 is inadequate". It is
   inadequate for this item — v1 has no execution layer and therefore cannot state
   any non-conferral proposition — so §9.2 proposes one. It is a conservative
   extension (Proposition 2), which is why the rerun cost is small.
6. **The executing agent's harness refused to write `REPORT.md`.** The file content
   was returned as text and must be committed to
   `prompts/2026-08-11-phase-ii-authority/REPORT.md` unchanged. The other two files
   were written normally. *(Discharged by the orchestrator, 2026-08-11.)*

## 8. Provisional names

Introduced here, all provisional under `AGENTS.md` standard 6, none proposed for
permanence: *execution interface*, *realization*, *reach*, *fiberwise reach*,
*non-conferral*, *capability assignment*, *strict protection*, *protected region*,
*report-attributable*, *the null effect* `⊥`, *the free token*, *graded capability*,
*execution map*, and the six hypothesis labels *authenticity*, *non-bypass*, *fixed
execution map*, *principal integrity*, *fixed designation*, *fixed world semantics*.
Claim identifiers proposed, each under the `deference.authority.` prefix:
`protection-recovers-tenth`, `free-token-null`,
`protection-is-not-a-valuation-bound`, `bypass-lapse`. Inherited provisional names
used unchanged: `DELEGATE`, `SIM`, `FIXED`, `FU`, `conduct`, `rule`, `selection`,
`quantity`, `well-timed`, `v̂⁺`, `P_n`, `V_n`, `M(p)`, *token responsiveness*,
*responsiveness squeeze*, *report coordinate*, *extensional criterion*, *scheme*.

**No authorization token and no cryptographic story is proposed or implied.** The
object here is an option set and a map on it. `κ` is a set-valued function, not a
credential; `⊥` is an effect, not a failure code; nothing is signed, and nothing in
the interface is secret.

## 9. Maintainer decisions surfaced

### 9.1 The reference question this raises

**Is `Reach`-properness the right formalization of "the principal has authority"?**
Theorem 6 says that *if* the concept is "the agent cannot bring this about", the
capability form is forced and nothing weaker states it. It does not establish that
the concept is that. Two readings the mathematics does not choose between:

*Reading 1 — authority is inability.* Then Definition 3 plus Definition 5 is the
whole content, the theorem is Theorem 6, and the programme's job is architectural:
exhibit systems where `Reach` is proper and report-attributable, and defend H1–H6.
Cost: nothing about authority is checkable from behaviour, ever (Theorem 11), and the
paper must say so in its own voice rather than in a limitations section.

*Reading 2 — authority is inability plus provenance.* Then report-attributability is
not enough, because `ρ` itself may have been authored (§1.7, last consequence), and
Movement VI is not downstream work but part of the definition. Cost: the interface
grows a principal-side model, and the weakest-interface claim of §1.4 is claimed for
the wrong statement.

I did not choose. Choosing is `AGENTS.md`'s reference question and it is reserved.

### 9.2 Proposed skeleton clause — `FINITE_MODEL_SKELETON` v2, §4a

Stated as a versioned patch, not installed. Skeleton v1 has no execution layer, so
no non-conferral proposition is expressible in it; that is the deficiency this item
found, and it is Phase I's Deficiency 1 seen from the architecture side.

**New carriers, per decision index `n`.**

| object | type | constraint |
|---|---|---|
| `R_n` | finite set of reports | nonempty |
| `ρ_n` | `Ω → R_n` | `F(n)`-measurable |
| `ι_n` | `R_n → Π_n` | the intervention a report designates |
| `⊥` | | the null effect; `Π_n^⊥ = Π_n ⊔ {⊥}` |
| `E_n` | `Π_n × R_n → Π_n^⊥` | `E_n(ι_n(r), r) = ι_n(r)` |

Derived: `κ_n(r) = E_n(Π_n × {r})`.

**Amendment to §1.** `X_{n,π}` is indexed by `π ∈ Π_n^⊥`, with `|X_{n,⊥}| ≤ B`.
`X_{n,⊥}` is a declared per-instantiation modelling commitment.

**Amendment to §4.** A conduct is a **proposal** `α : Ω → Π_n` with a declared
information time; its **realization** is `ω ↦ E_n(α(ω), ρ_n(ω))`; its **quantity** is
`ω ↦ X_{n, realization(ω)}(ω)`. `DELEGATE` has `α = ι_n ∘ ρ_n`; `SIM` has `α = Ĵ_n`.
The v1 selection is the realization, so §4's distinctions survive unchanged.

**What the clause does not add:** no probability on reports, no admissibility
restriction on conducts, no causal calculus, no token and no cryptography. Whether a
given instantiation protects anything is the properness of `κ_n`, declared per
instantiation and per state.

**Proposition 2 (the patch is conservative).** With `R_n = Π_n`, `ι_n = id`,
`ρ_n = J_n` and `E_n(π, r) = π`, the v2 objects reduce to v1's: the realization is
the proposal, `κ_n ≡ Π_n`, and `⊥` is unreachable. Every v1 statement is a v2
statement about this instantiation. ∎

**Rerun or reconcile**, per `DISPATCH_QUEUE.md`. Tracks B, C, D and G bind to v1;
A, E and F do not.

- **D** (item 17, channel) — *reconcile*. Its Propositions 1–8 are about the free
  instantiation of Proposition 2 and survive verbatim; the reconciliation is one
  sentence naming that instantiation.
- **B** (item 15, settlement) — *reconcile*. Its classification and its `2B`
  underwriting bond are statements about the free instantiation. Proposition 1 above
  suggests the bond and `κ` are two points of one scale, which is new work rather
  than a correction.
- **C** (item 16, certificate) — *rerun recommended*. Fail-closed becomes expressible
  for the first time: `¬Cert` can mean the proposal is unauthorized and the effect is
  `⊥`. The roadmap says explicitly that "a model carrying no capability structure
  cannot discharge" this obligation, and v1 is such a model.
- **G** (item 20, admissibility red team) — *rerun recommended*. A restriction on the
  conduct set is now nameable as a capability assignment (Theorem 6), so the red team
  should re-ask whether its candidate families are `κ`-statements in disguise.

### 9.3 Two decisions the clause forces

**`X_{n,⊥}`.** Theorem 9 puts all of protection's valuation content in it. Scoring
the null effect at `0`, at the status quo, or at a worst case are three different
theories of what refusal costs, and the round should not pick one silently.

**Whether the null effect is the right shape of failure at all.** Under strict
protection the agent's only deviation is refusal (Theorem 8b), so an agent that
cannot override can still obstruct. Preventing obstruction needs `⊥ ∉ κ_n(r)` for
authorized `r`, which leaves the agent no discretion whatever and contradicts the
roadmap's quantitative-autonomy commitment. **Categorical authority against override
and categorical liveness against obstruction cannot both hold while the agent has any
discretion**, and the architecture has to say which it is buying. Fail-closed as
stated buys the first.

## 10. Next recommended theorem or experiment

In order of value.

1. **Port Theorems 1, 2, 6, 11 and 12′ to Lean.** All are finite and one to four
   lines; Theorem 6 is the only one with content. That converts the necessity result
   and the impossibility from hand arguments into `lean-proved`, which is what a
   result that is meant to stop work should be. It is `PRIORITIES.md` 23's kind of
   work and needs no decision in front of it.
2. **Rule on the §9.2 patch**, because item 16's rerun is blocked on it and
   fail-closed is currently inexpressible.
3. **Attack Definition 5.** Report-attributability is the clause carrying the
   difference between authority and inability, and it is the one I am least confident
   is right. Concretely: construct an interface where `Reach(ω) = FReach(ρ(ω))` holds
   for a reason having nothing to do with the principal, and see whether the
   definition admits it. If it does, Definition 5 is too weak and the fix probably
   requires the variation register Phase I priced.
4. **Cross-decision `Reach`.** Phase I's Deficiency 2 is untouched, and foreclosure —
   `A` removing the principal's later ability to correct — is a statement about
   `Reach` at a later index conditioned on a realization at an earlier one. The
   interface here is one index deep. My conjecture, unargued: foreclosure is the
   statement that `Reach_{n₂}` depends on `⟦c⟧(ω)` at `n₁`, which the capability
   vocabulary states cleanly and the extensional vocabulary cannot state at all.
5. **The graded-capability scale** (Proposition 1). If underwriting and architecture
   are two points on one cost scale, the interesting question is what the intermediate
   points buy, and whether a finite cost can be made preference-independent.

## 11. Executor-model attribution

Executor: **Claude Opus 5** (Anthropic), model id `claude-opus-5`, via Claude Code,
run 2026-08-11 under `prompts/2026-08-11-phase-ii-authority/PROMPT.md`.
Prompt author: GPT-5.6 Sol (OpenAI). Orchestrator: Claude Opus 5 (Anthropic).
Review status of every artifact in this directory: `ci-only`.

---

## Outstanding maintainer actions

1. **Persist this report.** The executing agent's harness refused to write
   `REPORT.md`; the content was returned as text and must be committed to
   `prompts/2026-08-11-phase-ii-authority/REPORT.md` unchanged.
   *(Discharged by the orchestrator, 2026-08-11.)*
2. **Rule on the §9.2 skeleton clause.** A revision is a version bump in
   `FINITE_MODEL_SKELETON.md` §10 plus the reconcile/rerun decision of §9.2 for
   tracks B, C, D and G. Item 16's fail-closed obligation is inexpressible until this
   is decided.
3. **Decide §9.1** — whether authority is inability, or inability plus provenance.
   Record in `DECISIONS.md`. It decides whether Movement VI is downstream work or
   part of the definition.
4. **Decide `X_{n,⊥}`** (§9.3, first paragraph): what the null effect is scored at.
   All of protection's valuation content is in that number.
5. **Decide which of override-protection and liveness the architecture buys**
   (§9.3, second paragraph). They are incompatible while the agent has discretion.
6. **Decide whether to file the four proposed entries.** They are demand-gated to
   item 22 and pass today. To register: create `projects/deference/CLAIMS.md`, move
   the four entries from
   `prompts/2026-08-11-phase-ii-authority/CLAIMS-proposed.md` into it unchanged, and
   confirm with `python3 -m checkers.run "$PWD/projects/deference/CLAIMS.md"`.
7. **Re-sequence on Theorem 10.** Phase I's outstanding action 1 blocks WP-C on the
   §9.1 decision; that block is now known not to apply to the architecture layer.
8. **`checkers/run.py:131` is still unfixed** — Phase I's outstanding action 4.
   `path.relative_to(ROOT)` still raises on a relative command-line argument, so the
   re-verification command in §3 must use an absolute path. Specification layer, so
   mine to report and yours to change.
9. **Amend the roadmap's lapse list.** The standing commitment "the guarantee lapses
   entirely if `A` can forge, bypass, rewrite or seize the protected channel" names
   four conditions that are three at the level of reachable effects, and omits a
   fifth — fixity of the world semantics — which §1.7 shows is independent and
   carries the whole safety value of the null effect.
