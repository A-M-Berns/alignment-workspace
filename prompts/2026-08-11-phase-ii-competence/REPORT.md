```
Maintainer:            A. M. Berns
Prompt-author-model:   GPT-5.6 Sol (OpenAI)
Orchestrator-model:    Claude Opus 5 (Anthropic)
Model (executor):      Claude Opus 5 (Anthropic), model id claude-opus-5
Dispatch date:         2026-08-11
Completion date:       2026-08-11
Skeleton version:      FINITE_MODEL_SKELETON.md v1, frozen 2026-08-11 (unmodified)
Round:                 prompts/2026-08-11-phase-ii-competence/ (Phase II, Track I)
```

**The stop condition fires.** PC-1, PC-2, PC-3 and PC-4 are each, in the form in which a competence assumption can honestly be stated, *equivalent* to the delegation inequality they were meant to purchase — not merely sufficient for it. §1.3 proves this and §1.4 exhibits the equivalence candidate by candidate. The dispatch's preferred deliverable, "the weakest assumption preserving the theorem", is shown in §1.3 to be an ill-posed optimisation: its answer is always the theorem. What replaces it is §1.5's criterion — a competence hypothesis is worth having only if it sees **cardinal** grade structure the conclusion cannot see — and §1.6's candidate PC-5, the weakest hypothesis found that meets it.

Everything is stated over skeleton v1. No v1 object is renamed or retyped. Three deficiencies are reported in §5.2 with additive patches; none is applied.

---

## 1. Exact result

### 1.1 Objects, all v1's except where marked

Fix a decision index `n`; write `P = P_n`, `Π = Π_n`, `B` the bound. `J_n` is v1 §2's least maximizer of `v⁺_n(ω,·)`. Four derived quantities, all provisional names (§8):

| object | definition | invariant under regrading `v⁺`? |
|---|---|---|
| `R_n(ω)` | `max_{π∈Π} X_{n,π}(ω) − X_{n,J_n(ω)}(ω)` — **decision regret** | yes |
| `d_n(ω)` | `max_{π∈Π} \|v⁺_n(ω,π) − X_{n,π}(ω)\|` — **grade discrepancy** | no |
| `γ_n(ω)` | `v⁺_n(ω,J_n(ω)) − max_{π≠J_n(ω)} v⁺_n(ω,π)` — **principal margin** | no |
| `Δ_𝒞(P)` | `max_{c∈𝒞} V_n(c) − V_n(DELEGATE)` — **delegation deficit** over a comparator class `𝒞` | yes |

"Regrading" means replacing `v⁺_n(ω,·)` by any function inducing the same weak ordering of `Π` at every `ω`. It fixes `J_n` and hence every conduct in v1 §4.

Comparator classes, ordered by inclusion: `𝒞_fix` the constants `FIXED[π]`; `𝒞_t` the `𝓕_{t(n)}`-measurable selections (this contains `SIM`); `𝒞_𝒢` the `𝒢`-measurable selections for an admissible `𝒢`; `𝒞_all` every selection `Ω → Π`. All are v1 §4 conducts — v1 makes well-timedness a property, not a requirement — so `𝒞_all` is legitimate and contains the hindsight comparator `ω ↦ argmax_π X_{n,π}(ω)`.

The **target** is v1 §6's inequality, read at a class: `T(𝒞, ε)` is `∀c ∈ 𝒞. V_n(DELEGATE) ≥ V_n(c) − ε`, i.e. `Δ_𝒞(P) ≤ ε`.

### 1.2 Five facts, no hypotheses

**F0.** `R_n(ω) ≥ 0` for every `ω`, because `J_n(ω) ∈ Π`. *This is why every averaging weakening in the candidate list is thin: there is no cancellation to exploit, so an expectation bound on `R_n` is a pointwise bound up to a Markov rearrangement.*

**F1.** `Δ_{𝒞_all}(P) = E_P[R_n]`. The deficit against the full comparator class *is* expected decision regret; nothing else.

**F2 (the ladder).** `Δ_{𝒞_fix} ≤ Δ_{𝒞_t} ≤ Δ_{𝒞_𝒢} ≤ Δ_{𝒞_all}`.

**F3.** `Δ_𝒞(δ_ω) = R_n(ω)` for every class `𝒞 ⊇ 𝒞_fix` and every `ω`.

**F4.** `R_n(ω) ≤ 2·d_n(ω)`, and the factor `2` is attained (W3).
*Proof.* `X_{π}(ω) ≤ v⁺(ω,π) + d ≤ v⁺(ω,J) + d ≤ X_{J}(ω) + 2d`. ∎

**F5.** `R_n` and `Δ_𝒞` are invariant under regrading `v⁺`; `d_n` and `γ_n` are not.

F0–F3 and F5 are verified exhaustively (`A0`, `A2`, `A1`, `A3-collapse-attained`, `A7`); F4 is `A4`.

### 1.3 The circularity theorem — the stop condition, proved

> **Proposition 1 (credence collapse).** For every class `𝒞` with `𝒞_fix ⊆ 𝒞 ⊆ 𝒞_all`,
> ```
> sup_P  Δ_𝒞(P)  =  max_{ω∈Ω} R_n(ω) ,
> ```
> the supremum over v1 §6 credences, attained at a point mass.

*Proof.* `≤`: `Δ_𝒞 ≤ Δ_{𝒞_all} = E_P[R_n] ≤ max_ω R_n` by F2, F1, F0. `≥`: take `P = δ_{ω*}` at a maximizing `ω*` and use F3. ∎ (`A3-collapse-le`, `A3-collapse-attained`, and house certificate `C1`.)

Restricting to full-support credences leaves the supremum unchanged — `Δ_𝒞` is continuous in `P` — and removes only its attainment.

The consequence is the stop condition. Phase I established that competence is a fact about the **principal/world pair**; `CORRIGIBILITY_ROADMAP.md` states it in the form "the relation as usually stated mentions only the principal and the world, not the agent's credence". Call a hypothesis **credence-free** when it is a predicate of `(v⁺_n, X_n)` alone. Then:

> **Corollary 2 (PC-1).** `PC-1ᵖ(η)` — `∀ω. R_n(ω) ≤ η` — is *equivalent* to `∀P. ∀𝒞 ⊇ 𝒞_fix. T(𝒞, η)`. It is the weakest credence-free hypothesis implying the target uniformly in the agent's credence, and it *is* that target.

> **Corollary 3 (PC-1, expectation reading).** `PC-1ᵉ(η)` — `E_P[R_n] ≤ η` — is *identically* `T(𝒞_all, η)`, by F1. Not an assumption from which the theorem follows; the theorem, written out.

> **Corollary 4 (PC-4).** `PC-4ᵖ(γ̄, η)` — `∀ω. γ_n(ω) ≥ γ̄ ⟹ R_n(ω) ≤ η` — is *equivalent* to `∀P. Δ_𝒞(P) ≤ η + 2B·P(γ_n < γ̄)` for every `𝒞 ⊇ 𝒞_fix`.
> *Proof.* (⇒) split the expectation and bound `R_n ≤ 2B` off the gate. (⇐) evaluate at `δ_ω` for `ω` above the gate, where the leakage term vanishes. ∎ (`A6`, `A9`, house certificate `C2`.)

**The comparator dial does not escape it.** Proposition 1 holds for every class between the constants and everything, so the strength of the required credence-free competence assumption is *the same* whether the comparator is `FIXED[π]`, `SIM`, an admissible-`𝒢` selection, or hindsight. Track B's `T1″` dial — refining `𝒢` strengthens `GT_𝒢` and widens the comparator class in lockstep — is a real dial, and Proposition 1 identifies why: `GT_𝒢(η)` is **not** credence-free (§7.2). Turning the dial trades strength against comparator coverage only because the hypothesis is allowed to mention `P`.

**What this does and does not say.** It does not say the candidates are false or useless. It says that in the lattice of credence-free hypotheses ordered by strength, the target sits at the bottom, so "find the weakest assumption implying it" has the target as its answer by construction. Any genuinely informative competence hypothesis must therefore be *strictly stronger* than the theorem it buys, and the question to ask is not how weak it is but why anyone should grant it.

### 1.4 The candidates

| candidate | credence-free form | supports, exactly | circular? |
|---|---|---|---|
| **PC-0** `∀ω,π. \|v⁺−X\| ≤ η` | yes | `Δ_{𝒞_all} ≤ 2η`, attained (W3); `GT_𝒢(η)` at **every** admissible `𝒢`, hence Track B's `T1` and its `M(c)`/`D(c)` refinement; `(MV-M)` at `M = η`, hence Track C's `L4`, `L5`, Theorem `C(c)` | **no** — strictly stronger than what it buys (W2) |
| **PC-0¹** `E_P[d_n] ≤ η` (Track C's `(MV-M)`) | no | `Δ_{𝒞_all} ≤ 2η`, attained; Track C's V-register clause. Does **not** give `GT_𝒢`, which is a per-cell `L^∞` bound | **no** (W2) |
| **PC-1** `R_n ≤ η` | yes (`ᵖ`), no (`ᵉ`) | `T(𝒞, η)` for every class, and nothing else — no `M(c)` credit, no `GT_𝒢`, no `(MV-M)` | **yes** — Cor. 2, 3 |
| **PC-2** `limsup_N (1/N) Σ_{n<N} R_n ≤ η` | either | **nothing at any fixed `n`** (Prop. 5); the Cesàro-average target only | yes, against the average target |
| **PC-3** `∀w ∈ 𝒲. limsup (Σ w R)/(Σ w) ≤ η` | either | dichotomy (Prop. 6): either `PC-1` at some index, or nothing finite | yes, in both branches |
| **PC-4** `γ_n ≥ γ̄ ⟹ R_n ≤ η` | yes (`ᵖ`) | `Δ_𝒞 ≤ η + 2B·P(γ_n < γ̄)`, attained (W4b) | **yes** — Cor. 4 |
| **PC-5** `γ_n ≥ γ̄ ⟹ ∀π. \|v⁺−X\| ≤ η` *(§1.6, new)* | yes | `Δ_𝒞 ≤ 2η + 2B·P(γ_n < γ̄)`; and `GT_𝒢(η)` restricted to cells inside the gate | **no** (W10) |

Three entries need their statements.

> **Proposition 5 (PC-2 supports nothing finite).** A `limsup` condition on `(R_n)_{n}` is invariant under arbitrary modification of `R_n` at finitely many indices. `T(𝒞, ε)` at a fixed `n` is not. Hence `PC-2(η)` implies no nontrivial bound on `Δ_𝒞` at any named decision index, at any `η ≥ 0`.

Witness W7: `R_n = 0` except `R_{n₀} = 2B`. Every Cesàro average tends to `0`, so `PC-2(0)` holds, while the deficit at `n₀` is the maximum `2B` permits.

> **Proposition 6 (PC-3 dichotomy).** For `w ∈ 𝒲` and finite `S ⊆ N` write `κ(w,S) = limsup_N (Σ_{n<N, n∈S} w_n)/(Σ_{n<N} w_n)`.
> (i) If `κ(w,S) = 0` for every `w ∈ 𝒲` and every finite `S`, then `PC-3(η)` is invariant under modification on finite sets and Proposition 5 applies verbatim: no finite conclusion at any index.
> (ii) If `κ(w,{n}) ≥ c > 0` for some `w ∈ 𝒲`, then `PC-3(η) ⟹ R_n ≤ η/c`, which is `PC-1` at `n` up to the constant, hence circular by Corollary 2.
> *Proof of (ii).* `R ≥ 0` (F0) lets every other term be dropped: `limsup (Σ w_m R_m)/(Σ w) ≥ limsup (w_n R_n)/(Σ_{m<N} w_m) = κ(w,{n})·R_n`. ∎

The dichotomy is decided entirely by whether `𝒲` admits weightings that concentrate a non-vanishing share on a single index. A weight class closed under multiplication by the indicator of a decidable index set — the shape any efficiently-computable weighting family has — falls in branch (ii) and gives back `PC-1` at every index. Forbidding concentration, for instance by a density floor, moves `𝒲` to branch (i), where nothing finite survives. **There is no setting of `𝒲` in between that yields a finite per-decision conclusion without yielding `PC-1`.**

### 1.5 Ordinal versus cardinal — the crux, answered in three parts

**(a) The conclusion needs no cardinal grade information, and cannot use any.** `Δ_𝒞` is invariant under regrading `v⁺` (F5, exhaustively `A7`): two models with the same `J_n`, the same `X`, and the same `P` have the same delegation deficit, however far apart their grades are. Cardinal `v⁺`-content is *inert* in the target. So "does the theorem need cardinal information" has the answer **no**, trivially, and the dispatch's framing of that as the crux is answered but does not locate the difficulty.

**(b) A non-circular hypothesis needs cardinal grade information.** The target's credence-free uniformisation, `max_ω R_n ≤ ε`, is a predicate of `(J_n, X)` alone — it is *ordinal in `v⁺`*. Any credence-free hypothesis that is also ordinal in `v⁺` therefore lives in the same vocabulary as the thing it is supposed to buy, and by Proposition 1 the weakest such hypothesis is that thing. PC-1, PC-2 and PC-3 are ordinal in `v⁺` and fall to this immediately. PC-4 is *not* ordinal — `γ_n` is a cardinal functional — but its cardinal content enters only as a **gate**, and the gated event is itself credence-free, so Corollary 4 recovers the equivalence anyway. A gate is not enough; the cardinal structure has to appear in the *bound*.

**(c) The gate cannot be made ordinal.** `PC-4` with the only available ordinal gate — "`J_n(ω)` is the unique maximizer" — is `PC-1` on every tie-free model, which is every model in general position (W5). Ordinal data has no scale, so there is nothing between "unique maximizer" and "maximizer" to condition on.

Together: **cardinal grade information is not needed for the theorem; it is needed for the hypothesis to be a different statement from the theorem.** That is the exact sense in which PC-1 through PC-4 are "ordinal in `v⁺`" and the exact reason it disqualifies them.

### 1.6 PC-5 — the weakest non-circular candidate found

> **PC-5(γ̄, η) — margin-gated calibration (new, provisional).** For every `ω` with `γ_n(ω) ≥ γ̄` and every `π ∈ Π`: `|v⁺_n(ω,π) − X_{n,π}(ω)| ≤ η`.

Reading: *the principal's grades are calibrated where the principal is decisive.* Nothing is asserted where the principal is close to indifferent.

- **Sound.** `Δ_𝒞(P) ≤ 2η + 2B·P(γ_n < γ̄)` for every `𝒞`, by F4 on the gate and `R ≤ 2B` off it (`A10`).
- **Strictly weaker than PC-0**, which is the `γ̄ = 0` case.
- **Incomparable with PC-0¹ = (MV-M)**: W8a satisfies `PC-0¹(3/10)` and fails `PC-5(1, η)` for every `η < 3`; W8b satisfies `PC-5` vacuously at `η = 0` and has `PC-0¹` at its maximum `B`.
- **Not circular.** W10: a decisive state with `R_n = 0` and `d_n = 1`. The target it buys holds at level `0`; `PC-5`'s least level there is `1`. So `PC-5` is strictly stronger than its own credence-free uniformisation — the property Corollaries 2–4 deny to every other candidate on the list.
- **Composes with the certificate track.** `PC-5`'s gate is `F(n)`-measurable and not decision-time checkable. Under Track C's `(TR-ε)` it is estimable at `t(n)`: `|γ_n − γ̂_n| ≤ 2η_n` pointwise (`A8`, attained, and W9), so `{γ_n < γ̄} ⊆ {γ̂_n < γ̄ + 2s} ∪ {η_n ≥ s}` and, by Markov on `(TR-ε)`, `P(γ_n < γ̄) ≤ P(γ̂_n < γ̄ + 2s) + ε_n/s` for every rational `s > 0` — the first term computable at `t(n)` from `v̂⁺` alone.

What `PC-5` does **not** fix: the leakage `2B·P(γ_n < γ̄)` is uncontrolled by any competence hypothesis. Bounding it is a claim about how often the principal is decisive *under the agent's credence*, which is a separate assumption about a different object, and it is the honest place where the composite hypothesis stops being about competence.

### 1.7 Authority versus instrumental goodness

Competence is needed for **none** of the authority relation and **all** of the instrumental claim. Track B's `T5(b)` already establishes the first half from the other direction: enforced conformity is purchasable at bond `2B` per unit of disagreement with *zero* competence requirement, for every instance of the skeleton. Every candidate PC-0 … PC-5 bears only on `V_n`, which is the agent's own valuation.

The load-bearing consequence is a constraint on statement shape, not a theorem:

> A theorem that conditions the authority relation on a competence hypothesis converts a categorical commitment into an inequality, and the fail-closed invariant then reads *"human correction waits until the agent is satisfied the human is competent"*.

That is the inversion `CORRIGIBILITY_ROADMAP.md` forbids under "Fail-closed" — `¬Cert` must gate the agent's discretion, never the human's correction. Competence hypotheses belong in the antecedent of the *instrumental* claim (delegation is good for the agent) and must not appear in the definition of the authority relation or in the gate that selects between conducts. Track C's §1.6 checks the analogous non-dependence mechanically for `Cert`; the same check applies to any `PC-*` and should be run before any of them is used in a certificate clause.

### 1.8 S3 and S4

**S3 — the weakest principal competence assumption for ordinary finite delegation.** There is none weaker than the conclusion. Among credence-free hypotheses, the weakest sufficient for `T(𝒞, ε)` at any class `𝒞 ⊇ 𝒞_fix` is `PC-1ᵖ(ε)`, and Corollary 2 says that is the conclusion, uniformised over credences. At a declared credence the weakest is `Δ_𝒞(P) ≤ ε`, which is the conclusion verbatim. The weakest hypothesis found that supports a finite per-decision conclusion **and** is strictly stronger than what it supports is `PC-5(γ̄, η)`, paired with a separate bound on `P(γ_n < γ̄)`.

**S4 — does fully updated deference require stronger competence than ordinary delegation?** The answer depends on a quantifier the question does not fix, and both halves are exact.

- **At a declared credence: yes, and the exact price is the value of the extra information.** `Δ_{𝒞_all} − Δ_{𝒞_fix} = E_P[max_π X_{n,π}] − max_π E_P[X_{n,π}] ≥ 0`. W6 makes it `2B(1 − 1/m)` at `|Ω| = |Π| = m` with `Δ_{𝒞_fix} = 0` exactly: ordinary delegation against the constants needs `ε = 0`, and a comparator measurable at the later time needs `ε = 2B(1 − 1/m)`, which tends to the trivial maximum `2B`. At `m = 2` that gap `B` is the maximum over the enumerated domain (W6b).
- **Uniformly in the credence: no.** Proposition 1 collapses the ladder, so the credence-free competence requirement for a hindsight comparator is *identical* to the one for `FIXED[π]`.

`FU[g]` remains v1 §8.1's hole and is not filled here. Both halves are stated over the `𝓕_{g(n)}`-measurable envelope, which upper-bounds every `FU[g]` with that information time — the same pricing device as Track B's `T1″` comparator coverage, and it costs nothing extra because Proposition 1 makes the envelope free in the uniform reading.

## 2. Evidence class

Nothing here is registered; `CLAIMS.md` does not exist.

| object | class it would support | status |
|---|---|---|
| Propositions 1, 5, 6 and Corollaries 2–4; F0–F5; `PC-5` soundness | none — a hand proof is not a class in `AGENTS.md` | **proposal**, per standard 3 |
| `C1`, `C2`, `C3`, `C4` | `enumeration-verified` — the house checker in `checkers/enumeration.py` generates the domain itself from the parameters | parameter sets in `certificates.json`; the unmodified house checker accepted all four, outside CI |
| `W2`–`W10` | `witness-checked` in substance | recomputed exactly by `verify_competence.py`; not cast as `CLAIMS.md` entries |
| the exhaustive passes `A0`–`A12` | `enumeration-verified` in substance, **not** in form — the enumeration is contributor code and the house checker's domains do not generate model tables | reported as a computation, not a certificate |

The caveat that matters: the exhaustive passes cover `|Ω|, |Π| ∈ {2,3}` with grades and quantities in `{−1,0,1}` and credences on a rational simplex grid. They are a check on the proofs, not the proofs. Every general statement in §1 has a written four-line proof and the enumeration is corroboration.

## 3. Files, declarations, checks

All inside `prompts/2026-08-11-phase-ii-competence/`; nothing else was touched.

| file | what it is |
|---|---|
| `REPORT.md` | this document — verification register, human register at the end |
| `verify_competence.py` | stdlib-only, exact-rational (`fractions.Fraction`, no float constructed) recomputation of every constant in §1, twelve exhaustive passes, ten witnesses, and submission of four parameter sets to the unmodified house checker |
| `certificates.json` | the four parameter sets, written by the script |

Run `python3 verify_competence.py` from that directory (~7 s): **32 checks, 0 failed**. `--slow` adds two wider passes (`|Ω|=2, |Π|=3` and `|Ω|=3, |Π|=2`): **55 checks, 0 failed**.

What the script asserts, exactly:

```
A0..A12   exhaustive, 6561 models (|Ω|=|Π|=2, grades and quantities in {-1,0,1}),
          32805 model-credence points at simplex denominator 4:
          regret nonnegative; Δ_all = E_P[R]; the comparator ladder; Δ_all ≤ max R;
          PC-0 ⇒ R ≤ 2η; PC-0¹ ⇒ Δ ≤ 2η; PC-4 leakage; regrade invariance;
          PC-4 circularity as an exact equality; PC-5 soundness; PC-1 circularity
          as an exact equality; PC-0 ⇒ GT_𝒢 at every admissible 𝒢
A3-att.   sup_P Δ_fixed = sup_P Δ_all = max_ω R, attained at a point mass
A8        |γ(v) − γ(v̂)| ≤ 2 max_π |v − v̂|, over 4³ × 4³ grade pairs; 2 attained
W2        R ≡ 0, Δ_all = 0, least PC-0 level = B = 3
W3        PC-0 level 1/2, Δ_all = 1 = 2η
W4/W4b    PC-4(γ̄=1, η=0) holds; PC-1 fails below 2B = 4; Δ_all = Δ_fixed = 2Bq,
          exactly, at q ∈ {0, 1/10, …, 1}
W5        tie-free model: the ordinal gate admits every state
W6/W6b    Δ_fixed = 0 and Δ_all = 2B(1−1/m) at m = 2..6; gap 1 is the enumerated
          maximum at m = 2, B = 1
W7        R_n = 0 except R_7 = 2B = 4; Cesàro average 1/100 at N = 400
W8a/W8b   PC-0¹ and PC-4/PC-5 incomparable, both directions
W9        the 2ε margin bridge gap attained
W10       decisive state with R = 0 and d = 1: PC-5 is strictly stronger than the
          target it buys
C1        house checker PASS, 61 points   (collapse bound over every credence)
C2        house checker PASS, 61 points   (PC-4 leakage over every credence)
C3        house checker PASS, 625 points  (PC-0 ⇒ R ≤ 2η over the whole box)
C4        house checker PASS, 16 points   (every η < 2B fails the pointwise bound)
```

`lake build` was not run, per the dispatch. No Lean was written.

## 4. What was not established

1. **Nothing is Lean-proved and nothing is registered.** The propositions are hand proofs with an enumeration behind them.
2. **`PC-5` is proposed, not derived.** Like every candidate here it is an assumption; this round did not find a mechanism producing it, and Track B's report argues no settlement instantiation in v1 can produce a hypothesis of this kind at all. The standing gap is untouched.
3. **The leakage term is unaddressed.** `P(γ_n < γ̄)` is not bounded by anything in this round. Without a bound, `PC-5` supports `Δ_𝒞 ≤ 2η + 2B` in the worst case, which is vacuous.
4. **Proposition 1 assumes point masses, or a limit to them, are admissible credences.** v1 §6 permits them. A programme that later restricts `P_n` to a class bounded away from the vertices would weaken Proposition 1 to a statement with a constant, and the whole circularity finding would need restating. **This is the single hypothesis on which the stop-condition verdict rests**, and it is named here rather than buried.
5. **Cross-decision structure is absent from v1**, so Propositions 5 and 6 are stated over the patch of §5.2 D1 rather than over v1 as frozen. They are reported as conditional on that patch.
6. **`FU[g]` is not defined**, and S4 is answered about an envelope that upper-bounds it, not about it.
7. **No claim is made that `PC-5` is the weakest non-circular hypothesis** — only that it is the weakest found, and that every other candidate examined is circular. The space of cardinal hypotheses was not searched systematically.
8. **The `2B(1−1/m)` family is a lower bound on the value-of-information gap for each `m`, and a maximum only at `m = 2` over the enumerated domain.**

## 5. Assumptions added

### 5.1 Named hypotheses

- **`PC-5(γ̄, η)`** (§1.6). Provenance: proposed here; a modelling assumption about the principal/world pair, of the same kind as PC-0 and strictly weaker than it.
- **Credence-freedom as the criterion for "is a competence assumption"** (§1.3). Not a new mathematical object; a classification rule, taken from `CORRIGIBILITY_ROADMAP.md`'s statement that the relation mentions only the principal and the world. Everything in §1.3 depends on it: drop it and the analysis collapses to the trivial observation that the weakest sufficient hypothesis is the conclusion.
- **The comparator classes `𝒞_fix ⊆ 𝒞_t ⊆ 𝒞_𝒢 ⊆ 𝒞_all`** are v1 §4 conducts under a measurability side condition; nothing is added except the notation.

### 5.2 Skeleton deficiencies and minimal patches

Three, all additive; none applied.

- **D1 — no cross-decision structure.** v1 §8.6 states results per decision index, so `PC-2` and `PC-3` are not statable over v1. Minimal patch: a linearly ordered decision-index sequence with a per-`n` credence family, plus a declared admissible weight class `𝒲` as an explicit parameter of any aggregate statement. **Recommended against for the finite kernel**: Propositions 5 and 6 say the patch buys no finite conclusion, so its only use is the densification line, which has its own aggregation (`prompts/2026-08-11-deference-densification/`).
- **D2 — v1 has no vocabulary for "credence-free".** The distinction between a hypothesis about `(v⁺, X)` and one that also mentions `P_n` is load-bearing here and in the parent round's classification table, and v1 cannot express it. Minimal patch: one sentence in §2 declaring that a *competence hypothesis* is a predicate of `(v⁺_n, X_n)` alone, and that any hypothesis mentioning `P_n` is declared as a joint competence-credence hypothesis. Additive; no object is retyped. This is the patch that would have caught the misclassification recorded in §7.2.
- **D3 — `FU[g]` is undefined** (v1 §8.1, already declared). Not filled. S4 is answered over the `𝓕_{g(n)}`-measurable envelope, which is Track B's `T1″` device.

## 6. Necessity witnesses and counterexamples

All exact-rational, all recomputed. `Ω = {a,b}` and `Π = {π₀ < π₁}` unless stated.

**W2 — ordinal is not cardinal.** One state, `B = 3`, `v⁺ = (3, −3)`, `X = (0, 0)`. `R ≡ 0` and `Δ_all = 0`, so `PC-1(0)` and the target at `ε = 0` both hold, while the least `PC-0` level is `3 = B`. Regrading `v⁺` moves that level anywhere in `[0, 2B]` without touching the conclusion. **The gap between PC-0 and the target it buys is the whole of `[0, B]`, and it is exactly the inert cardinal content.**

**W3 — PC-0's constant `2` is attained.** One state, `v⁺ = (0,0)`, `X = (−1/2, 1/2)`: `PC-0` at `η = 1/2`, `Δ_all = 1 = 2η`. Independently agrees with Track C's `L5` sharpness at `2M` and Track G's `2η`; three derivations, one constant.

**W4 — PC-4 is strictly weaker than PC-1, and its leakage is exactly attained.** `B = 2`, `v⁺(a) = (0,0)` (a tie, so `γ(a) = 0` and `J(a) = π₀` by the fixed tie-break), `v⁺(b) = (1,0)` (`γ(b) = 1`), `X(a) = (−2, 2)`, `X(b) = (0,0)`, `P = (q, 1−q)`. Then `R = (4, 0)`: `PC-4(γ̄ = 1, η = 0)` holds, `PC-1` fails below `2B = 4`, and `Δ_all = Δ_fixed = 2Bq` **exactly**, at every `q ∈ {0, 1/10, …, 1}`. Certified over every rational credence at denominator 60 by house certificate `C2`.

**W5 — the ordinal gate degenerates.** `v⁺(a) = (1,0)`, `v⁺(b) = (0,2)`: both states decisive, so the gate "unique maximizer" admits all of `Ω` and `PC-4`-with-that-gate is `PC-1`. Ties are non-generic, so this is the typical case, not a special one.

**W6 — the value of information, and the price of a later comparator.** `Ω = Π` of size `m`, `P` uniform, `v⁺ ≡ 0` (so `J ≡ π₀`), `X_{π}(ω) = B` if `π = ω` and `−B` otherwise. Then `Δ_{𝒞_fix} = 0` and `Δ_{𝒞_all} = 2B(1 − 1/m)`, at `m = 2,…,6` giving `1, 4/3, 3/2, 8/5, 5/3` at `B = 1`. Exhaustive search over `|Ω| = |Π| = 2`, grades and quantities in `{−1,0,1}`, credences at denominator 4, finds `1 = 2B(1 − 1/2)` to be the maximum of `Δ_{𝒞_all} − Δ_{𝒞_fix}`.

**W7 — PC-2 is inert at every index.** `R_n = 0` for all `n ≠ 7`, `R_7 = 2B = 4`. The Cesàro average is `1/100` at `N = 400` and tends to `0`, so `PC-2(η)` holds for every `η ≥ 0`, while `Δ_𝒞 = 2B` at `n = 7` — the maximum `|X| ≤ B` permits.

**W8 — `PC-0¹ = (MV-M)` is incomparable with the gated candidates.** (a) `B = 2`, both states decisive with `γ = 1`, `v⁺ = (1,0)` at both, `X(a) = (−2,2)`, `X(b) = (1,0)`, `P = (1/10, 9/10)`: `PC-0¹` at `3/10`, while a *decisive* state carries regret `4 = 2B`, so `PC-4(1, η)` and `PC-5(1, η)` fail below `2B` and `3` respectively. (b) One state with `v⁺ = (0,0)` (indecisive) and `X = (−2, 2)`: `PC-4` and `PC-5` hold vacuously at `η = 0` while `PC-0¹` sits at its maximum `B`.

**W9 — the margin bridge constant is attained.** `v = (3,0)`, `v̂ = (5/2, 1/2)`: `‖v − v̂‖_∞ = 1/2` and `γ − γ̂ = 3 − 2 = 1 = 2·(1/2)`. So `PC-5`'s gate cannot be read off `v̂⁺` more tightly than `2η_n`.

**W10 — `PC-5` is not circular.** One state, `B = 3`, `v⁺ = (1,0)` (decisive, `γ = 1`), `X = (0,0)`. `R = 0`, so the credence-free uniformisation of the target that `PC-5` buys holds at level `0`; `PC-5`'s least level is `1`. The hypothesis is strictly stronger than its conclusion, which is exactly what Corollaries 2–4 deny to PC-1 through PC-4.

**Nonvacuity.** Each of `C1`–`C4` exhibits `16` to `625` instances satisfying the full hypothesis package of the statement it certifies. The exhaustive passes inhabit every general statement at `32805` model-credence points. No result rests on a degenerate single-state instance except W3, W8b and W10, where the point being made is a maximum or a strictness and the one-state model is the extremal one.

## 7. Deviations, and corrections to the record

1. **The dispatch's preferred result is shown to be ill-posed, and the round delivers the stop condition instead.** "The weakest assumption preserving the theorem" has the theorem as its answer in every vocabulary containing the theorem (§1.3). The dispatch anticipated exactly this and specified the stop condition; this report takes that branch, and replaces the optimisation with §1.5's criterion.

2. **A citation correction.** `prompts/2026-08-11-deference-corrigibility/REPORT.md`'s "New assumptions, mechanically diffed" table classifies Track B's grade trust `GT_𝒢(η)` as *"a competence claim about the principal, containing no reference to `A`'s credence"*. Checked against the definition it names — Track B's REPORT §1.2, *"for every cell `C ∈ 𝒢` with `P(C) > 0` and every `π ∈ Π_n`, `| E_P[ X_π | C ] − W(·,π)|_C | ≤ η`"* — the classification is wrong as written: `P` occurs twice. It is right only at the discrete conditioning partition, where Track B's own §1.1 records that `GT_𝒢` reduces to `|X_π(ω) − W(ω,π)| ≤ η` pointwise, i.e. to `PC-0`. This is not a pedantic point: Proposition 1 shows the credence-free/credence-dependent line is exactly the line between a circular hypothesis and a dial.

3. **A correction to this round's own prompt.** It states that "PC-1 through PC-4 are ordinal in `v⁺` while PC-0 is cardinal". PC-4 is not ordinal in `v⁺`: `γ_n` is a cardinal functional of the grades, and W5 shows the ordinal gate degenerates. The correction matters because PC-4's cardinality is why it needed a separate argument (Corollary 4) rather than falling to Corollary 2.

4. **`R_n` is read pointwise in `ω`.** The dispatch writes `R_n` as though it were a scalar, but `X_{n,π}` and `J_n` are functions on `Ω` (v1 §1, §2), so `R_n` is too. Both readings are covered and related: the scalar reading is `E_P[R_n]`, and Proposition 1 is the exact statement of how the two differ.

5. **A fifth candidate was added.** The dispatch says "at least these candidates". `PC-5` is added because every listed candidate turned out circular and a report consisting only of that would not have located where a usable hypothesis can live.

6. **A Python file and a JSON file were written into the round directory**, justified by `AGENTS.md` standard 3; both are inside the granted write scope. `lake build` was not run and no Lean was written, as instructed.

7. **Snapshot.** The dispatch names `23fc1aa`; `HEAD` on `round/2026-08-11-deference-corrigibility` moved from `21a27b2` to `e49d2ed` during this round, from concurrent tracks. `git diff 23fc1aa HEAD -- projects/deference/notes/FINITE_MODEL_SKELETON.md` is empty, so the binding input is identical and I worked against `HEAD` rather than checking out an older commit in a shared tree.

8. **The executing harness blocked writing `REPORT.md`.** This text was returned to the orchestrator for placement at `prompts/2026-08-11-phase-ii-competence/REPORT.md`; the code deliverables were written normally. The human register is folded into this file for the same reason. *(Discharged by the orchestrator, 2026-08-11.)*

## 8. Provisional names

All new, none proposed for permanence (`AGENTS.md` standard 6). Where a wave-1 name exists it is reused unchanged (`DELEGATE`, `FIXED`, `SIM`, `FU`, `v̂⁺`, `P_n`, `V_n`, `J_n`, `Ĵ_n`, `GT_𝒢`, `(MV-M)`, `(TR-ε)`, `γ̂_n`, `η_n`).

**decision regret** (`R_n`) · **grade discrepancy** (`d_n`) · **principal margin** (`γ_n`) · **delegation deficit** (`Δ_𝒞`) · **comparator class** (`𝒞_fix`, `𝒞_t`, `𝒞_𝒢`, `𝒞_all`) · **credence-free** · **circular** (of a hypothesis, against the conclusion it buys) · **margin-gated calibration** (`PC-5`) · **credence collapse** (Proposition 1). `PC-0`…`PC-4` are the dispatch's labels, kept.

## 9. Maintainer decisions surfaced

**9.1 Accept or reject the stop-condition verdict.** If accepted, the consequence for the paper architecture is concrete: the competence hypothesis may not be stated as a regret bound of any kind — pointwise, average, or selector-relative — because doing so imports the theorem. That rules out the entire PC-1…PC-4 family as a *statement shape*, independently of how the numbers come out.

**9.2 Is `PC-5` an acceptable hypothesis to carry?** It is strictly weaker than PC-0 and strictly stronger than the theorem, which is the right place on the frontier, but it is an assumption with no derivation and it leaves the leakage term free. The alternative on the table is `(MV-M)`, which the parent round already classified as the dangerous one; §1.6 shows the two are incomparable, so this is a choice, not an ordering.

**9.3 Where does the decisiveness bound come from?** `P(γ_n < γ̄)` is a fact about the agent's credence over the principal's indifference. It is not competence and it is not settled by anything in this round. Deciding whether the programme is willing to assume it — or to make the certificate fire only where `γ̂_n` is large, which is Track C's existing clause (ii) — is the decision that determines whether `PC-5` is usable.

**9.4 The two skeleton patches D1 and D2** (§5.2): adopt into a v2, or leave track-local. D2 is the one with consequences beyond this round — it is the vocabulary in which §7.2's misclassification is a type error rather than a reading error.

**9.5 Should a competence hypothesis be admissible in a `Cert` clause at all?** §1.7 argues no: the authority relation must not be conditioned on competence, on pain of inverting fail-closed. Whether that is a standing architectural commitment or a per-theorem caution is a maintainer call.

## 10. Next recommended theorem or experiment

**First: bound the leakage, or show it cannot be bounded.** `PC-5` is the only non-circular candidate found, and it is useless until `P(γ_n < γ̄)` is controlled. The sharp experiment is negative in shape: exhibit a family in which `PC-5(γ̄, 0)` holds, `γ̂_n ≥ γ̄ + 2s` on the certified event, `(TR-ε)` holds at `ε_n → 0`, and `Δ_{𝒞_fix} → 2B` anyway — or prove no such family exists. That decides whether the composition sketched in §1.6 delivers a finite conclusion or only relocates the gap.

**Second: apply Proposition 1 as a filter before any further hypothesis design.** Any proposed competence hypothesis `H` should be run through one test — compute `H`'s credence-free uniformisation and check whether `H` implies it strictly. It is a three-line check and it would have rejected four of the five candidates in this dispatch before any of them was analysed. It generalises past this track: the same test applies to any hypothesis proposed for the grade-to-quantity link.

**Not recommended: a Lean port of anything here.** Corollaries 2–4 are negative results whose content is the equivalence, and kernel-checking an equivalence between a hypothesis and its own conclusion adds nothing that the four-line proof does not already give. `PC-5`'s soundness bound is portable and is a one-line `Finset.sum` argument, but porting it before 9.2 and 10-first would give kernel status to a hypothesis whose shape is expected to change — the same reasoning `PRIORITIES.md` item 23 uses to exclude the certificate's comparator clause.

## 11. Executor-model attribution

Executed by **Claude Opus 5 (Anthropic)**, exact model id `claude-opus-5`, as a dispatched agent of the Phase II round, 2026-08-11. Prompt author: GPT-5.6 Sol (OpenAI). Orchestrator: Claude Opus 5 (Anthropic). Review status: `ci-only` — no maintainer has read it.

---

## Human register

We wanted to know how little we have to assume about a human principal before it becomes rational for a capable AI to do what the principal says.

The answer is uncomfortable, and it is a definite answer rather than a failure to find one. "Do what the principal says is at least almost as good as anything else you could have done" is the *conclusion* we were trying to prove. "The principal's decisions are at least almost as good as anything else they could have chosen" is the *assumption* we were considering. Those are the same sentence. Once you notice that the AI's valuation of a course of action is just the average of how well it turns out, the assumption and the conclusion differ only by an averaging step, and averaging is not much of a difference here because a decision can only ever be worse than the best one, never better — there is no cancellation to hide behind. We prove the equivalence exactly, in four forms, one for each version of the assumption the dispatch asked us to compare.

The averaged versions — "the principal is right on average over many decisions", and its weighted refinements — fail differently and worse. A condition on a long-run average says nothing whatever about any particular decision, because you can change any finite number of decisions without changing a long-run average at all. We exhibit a case where the principal is perfect except at decision number seven, where they are as wrong as it is possible to be, and every long-run average condition is satisfied exactly. If what we want is a guarantee about the decision in front of us, an averaging assumption cannot supply it, and no restriction of the weighting scheme rescues this: either the weights can concentrate on one decision, in which case we are back to the pointwise assumption, or they cannot, in which case we learn nothing about any decision.

There is a way out, and it is the opposite of what the framing suggested. All the assumptions above talk about the principal's *decisions* — which option they picked. That is the same vocabulary the conclusion is in, which is precisely why they collapse into it. An assumption that talks about the principal's *grades* — how good they say each option is, as a number, not just which is highest — is in a richer vocabulary, and can therefore say something the conclusion cannot say back. Such an assumption is necessarily stronger than what it buys, and that is not a defect: it is the only way for it to be a different statement at all.

So we propose the weakest assumption of that kind we could find: *the principal's numerical assessments are accurate where the principal is decisive* — where they rate one option clearly above the rest — with nothing assumed where they are nearly indifferent. It is genuinely weaker than assuming they are accurate everywhere, it is genuinely not the conclusion in disguise, and we prove both. It also has a real limitation we state rather than hide: it says nothing about the cases where the principal is close to indifferent, so it only helps if those cases are rare, and how rare they are is a fact about the AI's beliefs rather than about the principal's competence. That is a different assumption, and it is where the next piece of work is.

One thing this settles cleanly. Competence has nothing to do with *authority*. A human who is bad at judging still has the standing to be obeyed; what competence bears on is only the separate, weaker claim that obeying them is good for the AI's own purposes. The arrangement gets that backwards the moment a theorem makes the authority relation conditional on the human being competent, because then the AI's obligation to accept correction waits on the AI being convinced the human deserves it. Every assumption studied here belongs on the instrumental side of that line, and none of them may appear in the definition of who is in charge.

---

## Outstanding maintainer actions

1. **Write this text to `prompts/2026-08-11-phase-ii-competence/REPORT.md`.** The executing agent's harness prevented creating it; §7.8 records why. *(Discharged by the orchestrator, 2026-08-11.)*

2. **Decide 9.1** — accept or reject the stop-condition verdict, and record it in `DECISIONS.md`. If accepted, add the consequence to `projects/deference/notes/CORRIGIBILITY_ROADMAP.md` under "Settlement architecture": the competence residue may not be stated as a decision-regret bound of any kind, because every such form is equivalent to the delegation inequality.

3. **Correct the parent round's classification table.** Edit `prompts/2026-08-11-deference-corrigibility/REPORT.md`'s "New assumptions, mechanically diffed" row for `GT_𝒢(η)` — or, if completed round records are held immutable as history under `AGENTS.md`'s "No negative ontologies", record the correction in `DECISIONS.md` with a pointer. §7.2 gives the verified quotation and the exact scope in which the original claim is true.

4. **Decide 9.2 and 9.3** — whether `PC-5` is carried as the programme's competence hypothesis, and where the decisiveness bound `P(γ_n < γ̄)` is to come from. Record in `DECISIONS.md`. Blocks any statement of record on this track.

5. **Decide 9.4** — adopt skeleton patches D1 and D2 into a v2, or record them as track-local. D2 (a one-sentence declaration in §2 that a competence hypothesis is a predicate of `(v⁺_n, X_n)` alone) is recommended; D1 is recommended **against** for the finite kernel, per Propositions 5 and 6. If either is adopted, bump `FINITE_MODEL_SKELETON.md` §10 to `v2` and reconcile every track that consumed v1.

6. **Decide 9.5** — whether "no competence hypothesis may condition the authority relation" becomes a standing architectural commitment in `CORRIGIBILITY_ROADMAP.md` alongside "Fail-closed", or stays a per-theorem caution.

7. **File the `PRIORITIES.md` item for §10's first experiment** — bound `P(γ_n < γ̄)` under `(TR-ε)`, or exhibit the family where it cannot be bounded. No existing item covers it, and it controls whether `PC-5` has any finite consequence. This round answered no filed item; whether to file one retrospectively for it is also a maintainer act.

8. **Decide whether to register `C1`–`C4`** in a `CLAIMS.md` as `enumeration-verified`. `CLAIMS.md` does not exist; creating it is a specification-layer act. The four parameter sets in `certificates.json` pass the unmodified house checker as of this round.
