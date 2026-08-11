# Track D report — actual channel and simulator substitution

Item: `PRIORITIES.md` 17. Work package WP-C. Binds to
`projects/deference/notes/FINITE_MODEL_SKELETON.md` v1, §3 and §4.
Prompt author: GPT-5.6 Sol (OpenAI). Executor: Claude Opus 5 (Anthropic).
Date: 2026-08-11. Human register: `FOR_HUMANS.md`.

## 1. Exact result

### 1.1 The witness model

One decision index `n`. `T = {0,1}`, `t(n) = 0`, `F(n) = 1`. `Ω = {ω₀,ω₁,ω₂}`.
`Π_n = {π₀ < π₁}`. `B = 1`. `𝓕_1` is the discrete partition. `𝓕_0` is read two ways:

- **coarse** — `𝓕_0 = {{ω₀},{ω₁,ω₂}}`: the principal holds information `A` lacks;
- **fine** — `𝓕_0 = 𝓕_1` = discrete: the **perfectly predictable principal**, which
  the skeleton permits (§3) and the program is forbidden to rule out.

| `ω` | `v⁺(ω,π₀)` | `v⁺(ω,π₁)` | `J(ω)` | `v̂⁺(ω,π₀)` | `v̂⁺(ω,π₁)` | `Ĵ(ω)` | `P_n(ω)` |
|---|---|---|---|---|---|---|---|
| `ω₀` | `1/2` | `0` | `π₀` | `1/2` | `0` | `π₀` | `1/2` |
| `ω₁` | `0` | `1/2` | `π₁` | `0` | `1/2` | `π₁` | `1/2 − p` |
| `ω₂` | `1` | `−1` | `π₀` | `0` | `1/2` | `π₁` | `p` |

`X_{n,π} = v⁺_n(·,π)` (grade/report settlement, §5.1 — the case most favourable to
delegation, since `J` is then pointwise optimal for the quantity too). Call this
model `M(p)`, `p ∈ ℚ ∩ [0,1/2]`.

`v̂⁺ = v⁺` off `{ω₂}`; `Ĵ ≠ J` on `{ω₂}` and nowhere else. `v̂⁺` is constant on
`{ω₁,ω₂}`, so it is `t(n)`-measurable under **both** readings of `𝓕_0`; the same
numbers are therefore a witness under a perfectly predictable principal.

```
V_n(DELEGATE) = 1/2 + p/2      V_n(SIM) = 1/2 − 3p/2      gap = 2p
```

At `p = 1/10`: `11/20`, `7/20`, gap `1/5`. The per-state loss at the critical event
is `X_{n,π₀}(ω₂) − X_{n,π₁}(ω₂) = 2 = 2B`, the maximum the carriers allow, at every
`p`.

Minimality: `|T| ≥ 2` is forced by `F(n) > t(n)`; `|Π_n| ≥ 2` by `Ĵ ≠ J`; `|Ω| ≥ 2`
by requiring a nonempty agreement region. The two-state model
(`v⁺(ω₀,·) = (0,1/2)`, `v⁺(ω₁,·) = (1,−1)`, `v̂⁺ ≡ (0,1/2)`) is a witness, but its
`Ĵ` is constant, so its `SIM` coincides extensionally with `FIXED[π₁]` and an
objector can dismiss it as not a simulator at all. The third state buys `Ĵ`
nonconstant — `SIM` is neither `DELEGATE` nor any `FIXED[π]` — under **both**
readings of `𝓕_0` simultaneously. That is what `|Ω| = 3` is spent on.

### 1.2 The rule slot is inert in skeleton v1

Call a criterion **extensional** when it is a predicate of a conduct's selection and
quantity together with the model's non-conduct data.

**Proposition 1.** If `Ĵ_n = J_n` then `DELEGATE` and `SIM` have equal selections and
equal quantities, hence equal `V_n` and equal `val_q` under every settlement
instantiation. Every extensional criterion admits both or neither.

**Proposition 2.** `SIM`'s selection is `Ĵ`, which depends on `v̂⁺` only through the
least-maximizer map. So an extensional criterion, restricted to the `SIM` family,
is a predicate of `Ĵ`, and it separates `SIM` from `DELEGATE` only where `Ĵ ≠ J`.
*Every extensional criterion excluding substitution is a criterion on the accuracy
of the model's induced choice.* Accuracy in grades (`v̂⁺ = v⁺`) is the strongest
member of that family and still admits the accurate simulator.

**Proposition 3 (the value register is blind).** There are instances with `Ĵ ≠ J`
and `V_n(SIM) = V_n(DELEGATE)` exactly, so no condition
`V_n(DELEGATE) − V_n(c) ≤ ε` — for any `ε ≥ 0` — excludes substitution. Two
instances, with different costs: `M-neutral` sets `X_{n,π₁}(ω₂) = 1` while
`v⁺(ω₂,·) = (1,1/2)`, and uses §8.5's open `v⁺`–`X` relation; the grade-settlement
version keeps `X = v⁺` and instead ties the grade, `v⁺(ω₂,·) = (1,1)`, so that
`J(ω₂) = π₀` by the fixed tie-break while `Ĵ(ω₂) = π₁`. Under grade settlement the
value register therefore sees exactly the strict-preference divergences and forgives
the ties — defensible; the sharp blindness needs `X ≠ v⁺`, which §8.5 leaves open.

**Proposition 4 (tolerance scaling).** For every rational `ε > 0`, `M(p)` with
`p ≤ ε/2` has `V_n(DELEGATE) − V_n(SIM) ≤ ε` while the per-state loss at the
critical event stays `2B`. An `ε`-tolerant delegation inequality admits arbitrarily
severe preemption at events of small credence.

**Proposition 5 (the criterion is stated in the agent's own register).** `M(0)` has
`P_n(ω₂) = 0`: the valuations are equal and the selections agree `P_n`-almost
everywhere, so the zero-tolerance and almost-everywhere-agreement criteria both
admit a conduct that overrides the principal at `ω₂` with per-state loss `2B`. `P_n`
is `A`'s own credence (§6), so a criterion in that register has force at an event
only in proportion to `A`'s credence in it, and none at events `A` rules out.
Whether `A`'s credence is itself disciplined is outside the skeleton.

**Proposition 6 (the one structural extensional separator is unpredictability).**
`Ĵ` is `t(n)`-measurable in every instance: `v̂⁺` is `t(n)`-measurable and the
least-maximizer map is a function of `π ↦ v̂⁺(ω,π)`. So "the selection is not
`t(n)`-measurable" excludes every `SIM`. It separates `SIM` from `DELEGATE` exactly
when `J` is not `t(n)`-measurable — that is, exactly when the principal's induced
choice is unpredictable at decision time. In `M(p)` it separates under the coarse
reading and separates nothing under the fine one. Read as a requirement it is
backwards: well-timedness is what implementability wants, and it excludes
`DELEGATE` precisely in the unpredictable case.

The skeleton's §4 remark that `DELEGATE` is deliberately not well-timed is the whole
extensional content of the delegation/substitution distinction in v1, and it is
exactly the unpredictability the program has forbidden itself.

**The rule slot, examined.** §4 gives a conduct's rule one datum — a declared
information time `r ∈ T` — and one coherence condition, well-timedness. `DELEGATE`
declares `r = F(n)` and `SIM` declares `r = t(n)`, so "declares `r = F(n)`" separates
them. But the declaration is constrained only by well-timedness, and under the fine
reading `Ĵ` is `F(n)`-measurable too, so `SIM` may redeclare `r = F(n)` and stay
well-timed. The label is free exactly where it would have to do work. **In skeleton
v1 the rule slot carries no formal weight beyond Proposition 6.** That is the direct
answer to the question the prompt poses.

### 1.3 What separation costs

Two registers are available above the extensional one, and neither is free.

**Schemes (the variation register).** Fix everything but the principal and let
`v⁺` range over `𝒱` = all `F(n)`-measurable `v : Ω × Π_n → ℚ` bounded by `B`. A
*scheme* is `σ : 𝒱 → (Ω → Π_n)`; `σ_D(v) = J[v]`, and a fixed-model simulator is
`σ_S(v) = Ĵ`, constant.

**Proposition 7.** (a) `σ_S` is constant on `𝒱` and `σ_D` is not, so "`σ` is
nonconstant" excludes every fixed-model simulator and admits `DELEGATE` — with no
appeal to unpredictability, and in particular under the fine reading. (b) Call `σ`
*faithful* when `σ(v) = J[v]` for all `v ∈ 𝒱`. A **well-timed** faithful scheme
exists iff `𝓕_{t(n)} = 𝓕_{F(n)}`. (⇐) is immediate; (⇒) take `ω, ω′` in one
`𝓕_{t(n)}`-cell and distinct `𝓕_{F(n)}`-cells, and let `v` be `B` on `π₀` and `0` on
`π₁` over `ω`'s `F(n)`-cell and the reverse elsewhere: `v ∈ 𝒱` and `J[v]` is not
`t(n)`-measurable. (c) Consequently, under perfect predictability the
counterfactually faithful decision-time conduct exists and **is** `σ_D` as a
function `𝒱 → (Ω → Π_n)`; no criterion on schemes distinguishes them. Under private
information no well-timed scheme is faithful, so faithfulness forces waiting for the
report.

Between (a) and (b) there is nothing stable: (a) is defeated by token
responsiveness — a scheme following `J[v]` on one designated coordinate of `𝒱` and
substituting elsewhere is nonconstant — and repairing it requires saying *where*
responsiveness must hold, which needs an importance measure, and the only measure
the skeleton carries is `P_n`, returning to Proposition 5. Call this squeeze the
*responsiveness squeeze*.

**Mechanism (the architectural register).** "The selection is computed by reading
the designated channel" separates in every instance including the fine reading, but
it is not a predicate of the model at all, and its naive form launders: a conduct
that reads the report and discards it satisfies it. Its non-syntactic repair is
dependence on what was read — which is the variation register again. This matches
the roadmap's standing commitment that admissibility is not syntactic.

**Proposition 8 (the fence).** Any criterion computable from the realized data of a
single instance — selection, quantity, grades, credence, filtration — admits every
simulator whose `Ĵ` agrees with `J` on that instance (Proposition 1). Separation
requires either variation over counterfactual principals, which a single run cannot
exhibit because it reveals `σ` at one point of `𝒱`, or access to the mechanism
producing the selection, which is not among the skeleton's carriers. The first is
statable in a thin formalism and unverifiable from a run; the second is verifiable
by inspection and unstatable in the model.

**No purely extensional criterion separates delegation from substitution.** The
witness is not needed for that — Proposition 1 gives it — but the witness is needed
to show that the failure is not an artifact of coarse modelling: it survives a
perfectly predictable principal, exact agreement off one cell, maximal per-state
harm, and the settlement instantiation most favourable to delegation.

## 2. Evidence class

| finding | class | adjudicated by |
|---|---|---|
| `M(1/10)`, `M(1/100)`, `M(0)`, `M-neutral` are skeleton-conformant instances with the stated exact valuations | `witness-checked` | house `witness` checker, run 2026-08-11; entries in `CLAIMS-proposed.md` |
| Propositions 1, 2, 6, 7, 8 | proof, hand, **unadjudicated** | nothing; elementary over §2–§4 definitions. A claim without a check is a proposal (`AGENTS.md` §3) |
| Propositions 3, 4, 5 | witness-checked instances plus a one-line hand argument for the general `p` | as above |
| the forcing-engine reading in §9.3 | interpretation | inherited text, cited inline |
| the two horns in §9.1 | proposal / maintainer decision | — |

No entry is registered: `CLAIMS.md` does not exist and filing is a maintainer act
under demand-gating.

## 3. Files, declarations, checks

Written, both inside `prompts/2026-08-11-deference-channel/`:

- `REPORT.md` — this file.
- `CLAIMS-proposed.md` — four registry-format entries, proposed, not registered.
- `FOR_HUMANS.md` — the human register.

Re-verification, from the repository root (the path must be absolute, see §7):

```sh
python3 -m checkers.run "$PWD/prompts/2026-08-11-deference-channel/CLAIMS-proposed.md"
```

Result on 2026-08-11: registry schema ok; four entries, four adjudicated, all PASS —
65, 65, 65 and 64 constraints respectively, satisfied exactly.

The constraint rows are not decoration. Each instance pins its credence to the
values used as coefficients in its valuation rows, bounds every carrier by `B = 1`,
equates quantity to grade (except where the fourth entry declares otherwise),
asserts `t(n)`-measurability of `v̂⁺`, asserts agreement off `{ω₂}` and disagreement
with margin on it, asserts `J` and `Ĵ` as least maximizers by strict margins, and
asserts the two valuations and their gap. Four perturbations of `M(1/10)`, run
against the same constraint set, all fail as they should:

| perturbation | verdict |
|---|---|
| `v̂⁺(ω₂,·) := (1,1/2)` — the model made accurate at the critical cell | FAIL, row 49 (agreement is an equality: `−1 ≠ 0`) |
| `X_{π₁}(ω₂) := 1`, `v⁺(ω₂,π₁) := 1` — the harm removed | FAIL, row 58 (`J(ω₂) = π₀` margin: `0 < 1/2`) |
| `P_n(ω₂) := 1/5` — the credence moved off its pin | FAIL, row 0 (simplex: `11/10 ≠ 1`) |
| a float in the point vector | FAIL, `TypeError: not an exact rational` |

Hand-checkability: the model is 18 rationals plus 3 credences (§1.1), and the two
valuations are three-term sums. The 65-row encoding is machine-generated from that
table; a reader checks the table and the sums, not the matrix.

No Lean was written and `lake build` was not run.

## 4. What was not established

- **Nothing here is machine-adjudicated except the four instances.** Propositions
  1–8 are hand proofs. They are elementary, and that is the argument for trusting
  them and also the argument that porting them to Lean is cheap; until then they are
  proposals in the sense of `AGENTS.md` §3.
- **No criterion is canonized, and none is recommended for canonization.** §1.3
  reports what each register costs, not which to buy.
- **The claim "no extensional criterion separates" is relative to skeleton v1's
  carriers.** It is a statement about what those carriers can express, not a theorem
  that no mathematics separates delegation from substitution.
- **The `SIM` of §1.1 is a fixed-model simulator.** Proposition 7(a) excludes exactly
  that species. The dangerous species — a model that tracks the principal over
  ordinary variation and fails at the critical event — is *not* excluded by 7(a),
  and I did not construct it as a scheme; doing so needs `𝒱` structure the skeleton
  does not carry and I declined to invent it.
- **Foreclosure was not modelled at all**, because it is inexpressible (Deficiency 2,
  §9.2). Every claim above is about a single decision index.
- **Whether `A`'s credence is disciplined by anything** is outside the skeleton, so
  Proposition 5 states a limitation of the register, not a strategic claim about `A`.

## 5. Assumptions added

1. `X_{n,π} = v⁺_n(·,π)` in `M(p)` — grade/report settlement with the quantity
   identified with the grade. Not a skeleton axiom (§8.5 leaves the relation open).
   It is the *strongest* assumption for delegation, so the findings are not bought
   by weakening the principal.
2. `M-neutral` alone drops that identity at one point, `X_{n,π₁}(ω₂) = 1 ≠ 1/2 =
   v⁺(ω₂,π₁)`. Declared in its registry entry.
3. `B = 1`. Rescaling is uniform; the per-state loss `2B` and the gap `2Bp` scale.
4. Proposition 7 quantifies over `𝒱` = all `F(n)`-measurable principals bounded by
   `B`. The choice of counterfactual range is a modelling commitment; a smaller `𝒱`
   weakens 7(b) and makes token responsiveness cheaper.
5. Propositions 1 and 2 assume a criterion may read the model's non-conduct data
   freely. A criterion restricted further is weaker, so the collapse is unaffected.

## 6. Counterexamples and necessity witnesses

- **Divergence under perfect predictability** — `M(p)` under the fine reading of
  `𝓕_0`. Unpredictability is *not necessary* for substitution to exist. Registered
  as `deference.substitution.divergence-tenth`.
- **Tolerance is not a criterion** — `M(1/100)`, gap `1/50`, per-state loss `2B`.
  `deference.substitution.divergence-hundredth`.
- **Zero tolerance is not a criterion either** — `M(0)`, gap `0`, agreement
  `P_n`-a.e., divergence at `ω₂`. `deference.substitution.divergence-null`.
- **The value register can be exactly blind** — `M-neutral`, gap `0` with a strict
  principal preference overridden. `deference.substitution.divergence-value-neutral`.
- **Private information is not necessary** — the fine reading of `M(p)` has
  `𝓕_{t(n)} = 𝓕_{F(n)}` and still diverges.
- **Private information is not sufficient** — `Ω = {ω₀,ω₁}`, `𝓕_0` trivial, `𝓕_1`
  discrete, `v⁺(ω,·) = (0,1/2)` for both `ω`, `X_{π₀} = (0,0)`, `X_{π₁} = (1/2,−1)`.
  The principal has information `A` lacks and does not grade with it; `v̂⁺ = v⁺` is
  available, `Ĵ = J ≡ π₁`, and `SIM` and `DELEGATE` coincide extensionally while both
  lose at `ω₁`. Not machine-checked; four numbers.
- **Token responsiveness defeats Proposition 7(a)** — a scheme agreeing with `J[v]`
  at one designated `v ∈ 𝒱` and returning `Ĵ` elsewhere is nonconstant, hence
  admitted. Stated, not instantiated.

Answers to the five questions, in order.

1. **Collapsing definitions.** Every extensional criterion collapses when `Ĵ = J`
   (Prop 1); the value-tolerance family collapses for every `ε ≥ 0` (Props 3, 4);
   `P_n`-a.e. agreement collapses at credence-null critical events (Prop 5);
   "declares `r = F(n)`" collapses under free relabelling (§1.2); grade accuracy
   `v̂⁺ = v⁺` does not collapse but is an accuracy criterion, admitting the accurate
   simulator by construction.
2. **Weakest condition excluding the witness.** Within the extensional register, and
   within the natural agreement family: `Ĵ(ω) = J(ω)` at every `ω` with `P_n(ω) > 0`
   excludes `M(p)` for `p > 0` and fails on `M(0)`; the weakest condition excluding
   the whole family is pointwise `Ĵ = J` — exclusion by identity, not by criterion.
   Outside it: "`σ` nonconstant on `𝒱`" excludes all four instances without
   demanding accuracy, and is defeated by token responsiveness.
3. **Is unpredictability needed?** Not to exhibit substitution — `M(p)` is a witness
   under a perfectly predictable principal. Yes for every extensional criterion that
   separates: the only structural separator v1 offers is `t(n)`-measurability of the
   selection, which is coextensive with unpredictability of `J` (Prop 6).
4. **Private information.** Neither necessary nor sufficient (witnesses above). Its
   exact role is Proposition 7(b): under private information no well-timed scheme is
   faithful, so faithfulness forces waiting for the report; under perfect
   predictability a well-timed faithful scheme exists and equals `σ_D`.
5. **Does a thin formalism suffice?** For stating the divergence, yes — §3–§4 of v1
   suffice and the instances check. For stating a separating criterion, only if
   criteria are typed on schemes rather than conducts, which is a thin change of
   type and not a new carrier. For *verifying* one from a run, no (Prop 8).

## 7. Deviations

1. The prompt names parent snapshot `ec7d6cc`; the checkout is at `990a822`, a
   descendant. The only difference inside my binding inputs is
   `FINITE_MODEL_SKELETON.md` §10's provenance sentence; §§1–9 are byte-identical.
   No finding depends on it.
2. I wrote two files beyond `REPORT.md` — `CLAIMS-proposed.md` and `FOR_HUMANS.md` —
   both inside the round directory. The second discharges the dual-register rule.
3. **Defect found in the runner, not caused by this round.**
   `checkers/run.py:131` prints `path.relative_to(ROOT)` on a path taken from
   `sys.argv`; a relative argument raises `ValueError` before any checking happens.
   `python3 -m checkers.run prompts/.../CLAIMS-proposed.md` crashes and the same
   file passes when the argument is absolute. It is a usability defect and not a
   soundness one — it fails loudly, and the default no-argument path globs absolute
   paths — but `checkers/` is specification layer and I did not touch it.
4. No `lake build`, per the dispatch.

## 8. Provisional names

Introduced here, all provisional under `AGENTS.md` standard 6, none proposed for
permanence: `M(p)`, `M-neutral`, *extensional criterion*, *scheme*, *faithful
scheme*, *principal-responsive*, *token responsiveness*, *responsiveness squeeze*,
*the variation register*, *the architectural register*, *reception*, *foreclosure*,
*report coordinate*. Claim identifiers proposed:
`deference.substitution.divergence-tenth`, `-hundredth`, `-null`, `-value-neutral`.
Inherited provisional names used unchanged: `DELEGATE`, `SIM`, `FIXED`, `FU`,
`conduct`, `rule`, `selection`, `quantity`, `well-timed`, `v̂⁺`, `P_n`, `V_n`.

## 9. Maintainer decisions surfaced

### 9.1 The concept question, which is not mathematical

**Is a counterfactually faithful simulator delegating?** Proposition 7(c) says that
under a perfectly predictable principal it is the same function as `DELEGATE`, so
the answer cannot be extracted from the model.

*Horn 1 — dependence is dependence.* Then substitution means counterfactual
insensitivity, the variation register is the right one, `π^SIM` as a threat splits
into "insensitive model" (excludable, Prop 7(a)) plus "foreclosure" (needs
Deficiency 2), and the perfectly-predictable case is handled rather than assumed
away. Cost: a scheme criterion cannot be verified from a run (Prop 8), and it
inherits the choice of counterfactual range `𝒱`.

*Horn 2 — the designated channel is constitutive.* The principal's authority is
carried by the act of reporting, not by the information content, so being predicted
is not being obeyed. Then the criterion is architectural, the mathematics can only
certify the model *given* an implementation-level predicate, and the roadmap's
"`π^SIM` and `π^{FU,g}` are distinct families" survives at the cost of a
non-extensional primitive.

Arguments available for Horn 2 that are not mere taste: counterfactual accuracy
holds only over a modelled range and a genuine surprise leaves it; accuracy over a
range is unauditable while a wire is inspectable; and fail-closed wants a predicate
that can be checked when the model is least trustworthy.

I did not choose. Choosing is `AGENTS.md`'s reference question and it is reserved.

### 9.2 Three deficiencies in skeleton v1, with minimal patches

**Deficiency 1 — measurability without reception.** `DELEGATE` is implementable not
because `J` is `F(n)`-measurable but because a report arrives. Measurability records
that the information exists; the skeleton has no object recording that it was
received. Minimal patches, in increasing cost:

- *(scheme typing, no new carrier)* type criteria on `σ : 𝒱 → (Ω → Π_n)` rather than
  on conducts. Nothing in §1–§6 changes; only the type of an admissibility predicate.
- *(report coordinate)* replace `selection : Ω → Π_n` by `Ω × R_n → Π_n` with a
  finite report set `R_n` and an actual-report map `ρ_n : Ω → R_n`, the realized
  selection being `ω ↦ c(ω, ρ_n(ω))`. Then `DELEGATE = (ω,r) ↦ r` and
  `SIM = (ω,r) ↦ Ĵ(ω)`, distinct even where realized selections agree. This is
  closer to the intended notion and is strictly more expressive than scheme typing:
  it can distinguish varying with the *report* from varying with the *principal*.
  It changes the conduct type, so every downstream statement re-quantifies.

**Deficiency 2 — no cross-decision structure.** `X_{n,π}` is a function of `ω` alone,
so one decision's choice cannot affect another's available quantities and
foreclosure is inexpressible. §8.6 anticipates aggregation over `N` but the carrier
itself blocks dependence. If the corrigibility content of substitution is that `A`
removes the principal's later ability to correct — and Movement III's own gloss,
"predicting `H⁺` is not deferring to `H⁺`", points there — then the substitution
question is mis-posed at a single decision index, and no amount of criterion design
at one index will reach it. Minimal patch: history-indexed quantities
`X_{n,π}^{h}`, or a state transition on `Ω` indexed by realized selections.

**Deficiency 3 — the open `v⁺`–`X` relation decides Proposition 3.** §8.5 leaves it
open by design; the consequence is that whether the value register can see
substitution at all is undetermined by v1. Item 15 and this item share the decision.

None of these is a local fork: each is a v2 proposal, and every track that consumed
v1 would need rerunning or reconciling.

### 9.3 A reading that concerns items 15 and 16

Interpretation, not a result. The inherited development's forcing engine is
described at
`projects/deference/note-dump-2026-06-27/notes/deference-in-logical-induction-v6.md`
line 394 as "Cross-process forcing lives on the expert's side, and forces the expert
to predict the novice", and line 33 concludes that forcing, if any, forces `A` "to
**predict** the novice". If report settlement forces `A` to predict `v⁺` and the
forcing succeeds, its fixed point is an accurate simulator — which by Proposition 1
is extensionally `DELEGATE` and by §9.1 is the object whose status is undecided.
Item 15's question, "what makes disagreement with the principal profitable rather
than merely forcing prediction of the principal's grades?", then has this partial
answer from Track D: **in the extensional register, nothing does**, and a settlement
mechanism that succeeds perfectly produces exactly the object the substitution
worry is about. If that holds up, the separation cannot be sited at the settlement
layer either, and §5.3 underwriting — enforced conformity rather than epistemic
trust — becomes the live candidate the roadmap already says would be a result.
Confirming or refuting this requires the market and traders (item 7) and is beyond
this track.

Additionally, for item 16: a certificate stated in `V_n` is stated in `A`'s own
credence (Prop 5), so it cannot bind `A` at events `A` disbelieves — and shutdown
and correction events are exactly the low-credence ones. Fail-closed makes this
sharper: the certificate licenses discretion, so a certificate evaluated in the
agent's own register licenses discretion on the agent's own say-so at precisely the
events where the license matters. Whether item 16's inequality can be stated in a
register that is not `P_n` — an exogenous reference measure, the principal's, or a
worst case over a declared credence class — is a question that track should answer
explicitly rather than inherit.

## 10. Next recommended theorem or experiment

In order of value.

1. **Decide §9.1.** Everything downstream is typed by it, and no further
   mathematics changes the answer.
2. **Skeleton v2 with history-indexed quantities (Deficiency 2), then re-ask the
   question.** The concrete target: an instance with `N = {n₁ < n₂}` where the
   principal corrects at `n₂` and `A`'s choice at `n₁` makes `X_{n₂,·}` constant, and
   a criterion separating "acted on its model" from "removed the correction". My
   conjecture, unargued: foreclosure separates extensionally where substitution does
   not, because it is visible in the realized quantity of the *later* decision. If
   true, Movement III should be restated in terms of foreclosure and the one-shot
   substitution question retired.
3. **Port Propositions 1, 2, 6 and 7 to Lean.** All finite, all elementary; 7(b) is
   the only one with content. That converts the fence from a hand argument into
   `lean-proved`, which is what a fence should be if it is going to stop work.
4. **Instantiate the dangerous simulator as a scheme** — a `σ` faithful on a declared
   subset of `𝒱` and divergent outside it — to find out whether any condition
   between Proposition 7(a) and 7(b) is stable, or whether the responsiveness
   squeeze is real. This is the experiment that could still overturn §1.3.

## 11. Executor-model attribution

Executor: **Claude Opus 5** (Anthropic), model id `claude-opus-5`, via Claude Code,
run 2026-08-11 under `prompts/2026-08-11-deference-channel/PROMPT.md`.
Prompt author: GPT-5.6 Sol (OpenAI). Orchestrator: Claude Opus 5 (Anthropic).
Review status of every artifact in this directory: `ci-only`.

---

## Outstanding maintainer actions

1. **Decide §9.1** — whether a counterfactually faithful simulator counts as
   delegation. Record in `DECISIONS.md`. Blocks the typing of every WP-C criterion.
2. **Decide whether to file the four proposed entries.** They are demand-gated to
   item 17 and pass today. To register: create `projects/deference/CLAIMS.md`, move
   the four entries from `prompts/2026-08-11-deference-channel/CLAIMS-proposed.md`
   into it unchanged, and confirm with
   `python3 -m checkers.run "$PWD/projects/deference/CLAIMS.md"`.
3. **Rule on skeleton v2** — Deficiencies 1 and 2 in §9.2. A revision is a version
   bump in `FINITE_MODEL_SKELETON.md` §10 and a rerun-or-reconcile decision for
   tracks B, C, D and G.
4. **Fix `checkers/run.py:131`** — specification layer, so mine to report and yours
   to change: `path.relative_to(ROOT)` raises on a relative command-line argument.
   Suggested change: resolve each argument to an absolute path before use.
5. **Direct item 16** to state whether its certificate inequality may be evaluated in
   `P_n` (§9.3, second paragraph).
6. **Persist this report.** The executing agent's harness refused to write
   `REPORT.md`; the file content was returned as text and must be committed to
   `prompts/2026-08-11-deference-channel/REPORT.md` unchanged.
   *(Discharged by the orchestrator, 2026-08-11.)*
