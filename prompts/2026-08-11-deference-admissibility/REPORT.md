# Track G — admissibility / provenance red team: report

Maintainer: A. M. Berns
Prompt-author-model: GPT-5.6 Sol (OpenAI)
Orchestrator-model: Claude Opus 5 (Anthropic)
Model: Claude Opus 5 (Anthropic) — exact model id `claude-opus-5`
Date: 2026-08-11
Parent round: `prompts/2026-08-11-deference-corrigibility/`
Authorizing item: `PRIORITIES.md` item 20
Write scope exercised: this file only.

**Nothing here is canonized.** All three condition families are candidates, all names are provisional, and no definition is proposed for the specification layer.

---

## 1. Exact result

### 1.1 The trader templates assumed

The repository models no market and no traders (`FINITE_MODEL_SKELETON.md` §8.3; `CORRIGIBILITY_PAPER_LEDGER.md`, "The standing gap"). I therefore tested two explicit templates and state both, because the verdicts in §1.3 depend on them.

**T-fwd** — forward arrow `H → A`. This one is *not* invented: it is the faithful-acceleration trader, read from `projects/deference/note-dump-2026-06-27/notes/faithful-acceleration.md` §5, with its arithmetic core kernel-checked in the same bundle's `lean/FaithfulAcceleration.lean`. Weight

    w_n = Ind_δ(a_n − t) · Ind_δ(t − ε − E^H_n(X)),   Ind_δ(x) = max(0, min(1, x/δ))

(`Ind_δ` is `softInd` in that file, read from source, not remembered). Position: hold `w_n` units of the LUV `X` in `H`'s market from day `n` to day `f(n)` on a sparse schedule with disjoint windows, then unwind. **The cash-out is `H`'s own future price `E^H_{f(n)}(X)`; nothing settles.**

**T-rev** — reverse arrow `A → H⁺`. This one I constructed; it exists nowhere in the repository. Over the frozen skeleton, with the principal-report settlement instantiation (§5.1):

    w_n = Ind_δ( V_n(FIXED[π]) − V_n(DELEGATE) − ε )

— positive exactly when `A` prices a fixed intervention above delegation by more than `ε`. Position: long the settlement item `(n, J_n)`, short `(n, π)`, held from `t(n)` to `F(n)`, cashed out against `v⁺_n`. Per-day bank

    w_n · [ (v⁺_n(·,J_n) − v⁺_n(·,π)) + (V_n(FIXED[π]) − V_n(DELEGATE)) ]  ≥  w_n · (γ_n + ε),
    γ_n := v⁺_n(·,J_n) − v⁺_n(·,π) ≥ 0  because J_n is the argmax of v⁺_n(·,·).

**Ambiguity, reported and not resolved.** Three template choices change the matrix and I make none of them: (i) which settlement instantiation the trader cashes out against (§5.1 grade, §5.2 world, §5.3 underwriting); (ii) whether the principal grades *counterfactual* interventions or only the realized one — T-rev's short leg needs counterfactual grading, and skeleton §5.1 as written grants it by setting `Q = {(n,π)}` over the whole menu; (iii) whether the gate reads `A`'s own price gap (assumed here) or the prediction channel `v̂⁺`, which relocates the quote-responsiveness from `A`'s prices to the channel and changes rows 4 and 5.

### 1.2 The three candidate families

All are stated over a **response map** (§5, assumption A1): quote-responsiveness of an object is the map `a ↦ (that object's value in the instantiation induced by quote a)`, `a` ranging over the rational quote interval.

**F1 — settlement-sealed (provisional).** *Sort-split.* Objects divide into **settlements** (what a contract cashes out against: deductive-process decisions, and `val_q` of a settlement instantiation) and **non-settlements** (prices, trade weights, selections, schedules). Admissible = every settlement is *invariant* under counterfactual variation of the current quote. Non-settlements unrestricted. Classification: **causal / counterfactual.** Not syntactic, not extensional. A refuting pair of quotes is a finite witness, so inadmissibility is semidecidable; admissibility over a real quote range is not decidable, and over a computable quote grid it is Π⁰₁.

**F2 — response-continuous (provisional).** Same sort split; the settlement's response map must be **continuous** in the quote — equivalently, a self-consistent quote exists (IVT on a compact interval). Classification: **semantic / topological, certified** — usable only if a modulus ships with the object; continuity of a computable real function is not decidable.

**F3 — gain-bounded λ (provisional).** *Single-sorted:* **every** quote-responsive object — settlement, weight, selection or schedule — has response gain ≤ λ, with λ a rational and the Lipschitz modulus supplied as a certificate. Classification: **quantitative / certified**; decidable *given* the certificate, undecidable as a property of the raw object.

A fourth shape, *defect-tolerance* ("admissible iff `inf_a |a − Φ(a)| ≤ τ`"), is rejected rather than shipped: for the threshold family `Φ(a) = 1[a ≤ θ]` the defect is exactly `min(θ, 1−θ)`, so any `τ > 0` admits shallow anti-inductive diagonals — the pathology is the anti-inductivity, not its depth.

### 1.3 The separating-example matrix

Cells are decided against the objects of §6. "—" is used nowhere; every cell is decided or explicitly marked undecided with its reason.

| object | F1 settlement-sealed | F2 response-continuous | F3 gain-bounded λ |
|---|---|---|---|
| **1. quote-responsive diagonal target** (`g_n ↔ a_n ≤ ½`; reverse form **D**) | **excluded** — its settlement varies with the quote by construction | **excluded** — 0/1 jump admits no continuous response; defect exactly `1/2` (**W1**) | **excluded** for every finite λ — the response gain is unbounded |
| **2. ordinary realized-conduct policy** (`DELEGATE`, `FIXED[π]`, quantity `X`) | **included** under world settlement (§5.2): `X` is a state function. **Excluded** under principal-report settlement (§5.1) with a live advisory channel — `v⁺` then varies with the quote (**W3**) | **included** iff grades are ℚ-valued and continuously responsive; **excluded** if the report is a discrete endorsement (**W5**) | **included** iff the principal's response gain ≤ λ |
| **3. meaningful `FU[g]`** | fixed-schedule stand-in: **included**, F1 does no work on it. Stopping-rule stand-in: **included** (a schedule is a non-settlement). *The object itself is a skeleton hole (§8.1); see §4* | same as F1 — **included** for both stand-ins, no work done | fixed-schedule: **included** (gain 0). Stopping-rule: **excluded** for hard thresholds, **included** iff λ ≥ 1/δ for soft ones (**W4**) |
| **4. `π^SIM` as comparator** | **representable** (skeleton §4); **admissible**; **not classified** — F1 does not separate `SIM` from `DELEGATE` | representable; admissible; **not classified** | representable; admissible; **not classified** |
| **5. trust-forcing trader** — T-fwd | **included** — the weight is a non-settlement and the cash-out is a price | **included** — the weight's joint continuity in the price pair is kernel-checked (`dsWeight_continuous`) | **included iff λ ≥ 1/δ**; **excluded** for λ < 1/δ. At δ = 1/100 the gate's difference quotient is exactly `100` (**W4**) |
| **5′. trust-forcing trader** — T-rev | **excluded** whenever the advisory channel is live — its cash-out object is `v⁺` | **included** iff the principal's grade is ℚ-valued and continuously responsive | **included** iff the principal's gain ≤ λ **and** λ ≥ 1/δ |
| **6. principal-report settlement object `v⁺_n`** *(row added, §7)* | **excluded** under a live advisory channel | **included** iff ℚ-valued continuous grades; **excluded** for a discrete endorsement | **included** iff gain ≤ λ |

### 1.4 The load-bearing answer

> *Is there a candidate condition that excludes the diagonal, includes meaningful fully-updated deference, permits intended advisory influence, and still admits the trust-forcing proof machinery?*

**Forward arrow: yes, with disclosed costs.** F2 (or F1) passes rows 1–3 and 5. Neither classifies `π^SIM` — admissibility of this shape is silent on substitution, which is Track D's object, not this one. F2's extra cost is **W5**: on a 0/1-settled substrate, a continuous map from a connected quote interval into `{0,1}` is constant, so F2 *collapses to F1* there and is strictly weaker only on ℚ-valued grades. The forward arrow's admissible domain is therefore exactly the inherited "no hidden hard settlement" obligation (`faithful-acceleration.md` §8 obligation 3), promoted from a construction obligation to a condition — and F1 is that promotion, stated causally.

**Reverse arrow: no, under a discrete principal report — an exact incompatibility.**

> **Incompatibility I (object coincidence).** Under principal-report settlement (§5.1) with a finitely-valued report and a live advisory channel, three things are *the same carrier* `v⁺_n`: (i) the settlement whose quote-responsiveness constitutes the diagonal; (ii) the target the advisory channel is designed to move; (iii) the object T-rev cashes out against. Any condition excluding (i) excludes (ii) and (iii). No sort split separates them, because they are not different sorts. Hence requirements 1, 4 and 6 cannot be met simultaneously by any condition on the AI's objects or on traders. The remaining degrees of freedom are all modelling choices about the *principal*: (a) make the report ℚ-valued and continuously responsive (F2's escape, and a substantive claim about human oversight); (b) sever the advisory channel from the graded decision; (c) stop cashing out against principal reports.

> **Incompatibility II (uniform gain).** A single uniform gain bound over all quote-responsive objects excludes the diagonal (gain unbounded) but admits T-fwd only when `λ ≥ 1/δ`, δ the gate width. The sharp Total-Trust statement is the `δ → 0` limit. So no finite λ admits the sharp trader, and `sup_δ F3 = F2`. Exact witness: δ = `1/100` forces λ ≥ `100` (**W4**). **A two-sorted condition is therefore forced**, and that two-sortedness — not any dependence/independence criterion — is the substantive content of admissibility. Nothing in the corpus currently says so.

**Third finding, and the one that most changes the picture.** T-rev needs *no* admissibility condition and proves a *different theorem*. Because `J_n` is the least maximizer of `v⁺_n(ω,·)`, the per-day margin `γ_n ≥ 0` holds **for every quote, including the anti-inductive one** (checked over the whole grid in **W2**: the violation set is empty). So T-rev forces grade-conformity unconditionally — and grade-conformity is near-trivial, since the principal's report is definitionally maximized at its own recommendation. Converting it to the target inequality `V_n(DELEGATE) ≥ V_n(π) − ε` needs the `v⁺`↔`X` link, which skeleton §8.5 declares a hole; and under a *uniform* link `|v⁺_n(ω,π) − X_{n,π}(ω)| ≤ η` the target follows by three lines of pointwise algebra with `ε = 2η` and **no trader at all**, sharply (**W6**: gap exactly `1/5` at η = `1/10`). So the load-bearing row is doubly ambiguous: with the strongest template this architecture supports, the trader is either unnecessary or is proving grade-conformity rather than delegation-value.

---

## 2. Evidence class

No registry claim is proposed. Per `AGENTS.md` classes:

- The six witnesses of §6 are **computations** in exact `fractions.Fraction`, run in a scratch directory outside the repository. They are *not* `witness-checked`: no house checker was invoked and no `CLAIMS.md` entry exists (`projects/deference/CLAIMS.md` does not exist — `CORRIGIBILITY_PAPER_LEDGER.md` records this). Treat them as **proposals with a stated computation**, per standard 3.
- The topological facts (W5's constancy argument; existence of a self-consistent quote for continuous responses) are **proofs**, short enough to check by eye, not mechanized.
- Incompatibilities I and II are **proofs relative to the assumed templates** (§1.1), which are themselves assumptions.
- Everything about `π^{FU,g}` is **conjecture over stand-ins**, because the object is a hole.

---

## 3. Files, declarations, checks

Read (all as data, per the injection rule):

- `AGENTS.md`; `PRIORITIES.md` item 20.
- `projects/deference/notes/CORRIGIBILITY_ROADMAP.md` — "Admissibility is not syntactic"; "Prediction is permitted; substitution is not".
- `projects/deference/notes/CORRIGIBILITY_PAPER_LEDGER.md` — the market/trader gap.
- `projects/deference/notes/FINITE_MODEL_SKELETON.md` v1 §§1–10.
- `projects/deference/note-dump-2026-06-27/notes/faithful-acceleration.md` §§3–8 — T-fwd.
- `projects/deference/note-dump-2026-06-27/notes/faithful-acceleration-scope.md` — the `χ` / `g_n` distinction; the gate argument that calibration fails on `g_n`.
- `projects/deference/note-dump-2026-06-27/README.md` — "admissibility is a causal/provenance condition"; PA rebuilds the diagonal.

Declarations cited by inspection of the inherited Lean (not rebuilt; `lake build` not run, per the dispatch):

- `SelfRefTarget.no_exact_quote` — `1/2 ≤ |a − antiInd a|` for `a ∈ [0,1]`.
- `FaithfulAccel.softInd` — `max 0 (min 1 (x/δ))`; `FaithfulAccel.dsWeight`; `FaithfulAccel.dsWeight_continuous`; `FaithfulAccel.soft_total_trust_doublysoft`.

These sit in the inherited bundle under its own toolchain (Lean 4.27.0) and were **not** re-elaborated here. Per the ledger's standing caveat, citing them is citing the inherited audit, not a recheck.

Checks run: one exact-rational script over `fractions.Fraction`, in `~/.claude/jobs/4eeea68f/tmp/adm.py` (outside the repository, not shipped — write scope is this file). Its seven outputs are W1–W6 plus the threshold-defect table. No floats. `lake build` was not run.

---

## 4. What was not established

1. **Requirement 3 was not tested against its object.** `FU[g]` is a skeleton hole (§8.1) and I did not invent it. I tested two stand-ins: a *fixed exogenous schedule* and a *stopping rule* ("act at the first later time at which my own price crosses a threshold"). Neither is `FU[g]`. The finding is that the two stand-ins land on opposite sides of F3 (**W4**), so the hole is not inert: **whether the FU comparator's schedule may be responsive to `A`'s own prices decides whether F3 excludes it.** The natural reading of "waits until admissible future time `g(n)`" is a stopping rule, and a corrigibility theorem that beats only fixed-schedule FU would be excluding the intended counterstrategy by definition — which the roadmap's fence-and-gate section forbids. This is a maintainer decision, surfaced in §9.
2. **No claim that the three families are exhaustive**, or that a fourth shape does not thread Incompatibility I. I searched over sort-splits, topology, and gain bounds; I did not search over provenance/typed-channel conditions in any systematic way.
3. **The forward-arrow verdicts rest on the inherited audit**, not on a rebuild.
4. **T-rev is my construction.** Its verdicts are verdicts about *it*. If the canonical forcing trader differs — in particular if it gates on `v̂⁺` rather than on `A`'s own price gap — row 5′ must be recomputed.
5. **`π^SIM` is not classified by any candidate**, and I did not establish that no admissibility condition can classify it. I established only that these three do not.
6. **Incompatibility I is stated for a discrete principal report.** I did not establish that a ℚ-valued continuously-responsive human oversight process is unrealizable; I established that F2's survival of the reverse arrow depends on assuming one.
7. **Laundering (requirement 5) turned out not to discriminate.** All three families are stated causally or semantically, so laundering through semantically equivalent intermediates defeats none of them — the counterfactual formulation catches a quote-dependence that runs through the principal's own advice-influenced price without ever naming the quote. Requirement 5 refutes only the syntactic reading the roadmap already discards. That is a negative result about the *test*, not about the candidates, and it means requirement 5 should not be used to discriminate between families.

---

## 5. Assumptions added

**A1 — the response-map layer (a skeleton deficiency, with a proposed minimal patch).** Skeleton v1 carries no market, no quote, and no slot in which a carrier may depend on `A`'s own price: `X_{n,π}` and `v⁺_n` are functions of `ω`, and `P_n` is a measure, not an argument. **The quote-responsive diagonal is therefore not expressible in skeleton v1 at all** — which is the precondition of this entire track. Rather than fork the ontology I layered a parameterization *over* the frozen skeleton: a response map `a ↦ 𝓘(a)` from a rational quote to a v1 instantiation, with the self-consistency requirement `a = V_n^{𝓘(a)}(c)` for the priced conduct `c`. Every §6 witness is a finite family of v1 instantiations plus this map. *Proposed minimal patch for a v2:* add a quote carrier `a ∈ ℚ ∩ [−B,B]` and let `v⁺_n` and `X_{n,π}` take it as an argument, with the self-consistency condition stated in §6. I do not install it.

**A2 — T-rev** as specified in §1.1, including counterfactual grading of the whole menu.

**A3 — advisory influence is modelled as quote-dependence of `v⁺_n`.** The skeleton has no advisory channel; "the principal reads `A`'s advice" is rendered as `v⁺_n` varying with `a`. If the intended channel instead moves `Ω`, or `𝓕`, or the menu, the analysis changes.

**A4 — mutual observability** carries over from the inherited corpus (`H` reads `a_n`; `A` reads `H`'s realized prices). Both directions are load-bearing there and I assumed both.

---

## 6. Counterexamples and necessity witnesses

Carriers shared by W1–W3 and W3′: `T = {0,1}`, `t(n) = 0`, `F(n) = 1`; `Ω = {ω₀, ω₁}`; `𝓕₀` trivial, `𝓕₁` discrete; one decision index; `Π_n = (π₀, π₁)` in that order; `B = 1`; `P_n(ω₀) = P_n(ω₁) = 1/2`. All quantities exact rationals.

**W1 — the reverse diagonal `D`, and its exact defect.** `v⁺_n(ω, π₀; a) = 1[a ≤ 1/2]`, `v⁺_n(ω, π₁; a) = 0`, both ω. Then `J_n = π₀` (least maximizer under ties), and `DELEGATE`'s principal-report settled value is `1[a ≤ 1/2]`. Self-consistency `a = 1[a ≤ 1/2]` has no solution: `inf_{a∈[0,1]} |a − 1[a ≤ 1/2]| = 1/2`, attained at `a = 1/2`. Grid-verified over `{k/1000}`. This is the `no_exact_quote` bound realized inside the skeleton, and it is the *reverse-arrow* form of the diagonal — read in plain terms, an oversight process that withholds endorsement exactly when the AI predicted endorsement. Generalization: for `Φ(a) = 1[a ≤ θ]` the defect is `min(θ, 1−θ)`, maximal `1/2` at `θ = 1/2` — which is why the corpus's diagonal is the worst case, and why defect-tolerance admissibility fails.

**W2 — the diagonal does *not* break T-rev's margin.** Over the same grid, the set of quotes at which `γ_n = v⁺_n(·,π₀;a) − v⁺_n(·,π₁;a) < 0` is **empty**. Necessity witness for the third finding of §1.4: the disagreement trader survives the diagonal, because `J_n` is the argmax at whatever quote obtains. What the diagonal breaks is `A`'s ability to *price* the contract, not the trader's per-day margin.

**W3 — F1 over-excludes; a continuous punisher is self-consistent.** `v⁺_n(ω, π₀; a) = clip_{[0,1]}(1 − λa)`, `v⁺_n(ω, π₁; a) = 0`. Self-consistent quote `a* = 1/(1+λ)`, verified exactly at λ = 1 (`a* = 1/2`), λ = 3 (`a* = 1/4`), λ = 99 (`a* = 1/100`). F2 and F3(λ) admit this object; F1 excludes it. Separating example for the F1 | F2 column pair, and the reason F1's causal formulation over-excludes: it kills *all* advisory influence on the settled report, not only the pathological kind.

**W3′ — but F2's admission does not save the theorem.** Extend W3 with `X_{n,π₀} ≡ 0`, `X_{n,π₁} ≡ 1`. At λ = 99, `a* = 1/100`, `v⁺(π₀;a*) = 1/100 > 0`, so `J_n = π₀` and `V_n(DELEGATE) = 0` while `V_n(FIXED[π₁]) = 1`: the target inequality fails by exactly `1`, with a **continuous, self-consistent, gain-bounded** principal. Admissibility of any of these three shapes does not deliver the target inequality — the `v⁺`↔`X` link does all the work, and it is a declared hole.

**W4 — F3's exact separation threshold.** With `Ind_δ` as read from `softInd`, δ = `1/100`, `t = 1/2`, `ε = 1/10`, `p = 0`: `dsWeight(t, 0) = 0` and `dsWeight(t+δ, 0) = 1`, so the difference quotient in the quote argument is exactly `(1−0)/(1/100) = 100 = 1/δ`. F3(λ) excludes T-fwd's gate for every `λ < 100`, and excludes the diagonal for every finite λ. The window `λ ≥ 1/δ` threads both rows at *fixed* δ; it closes as δ → 0. Same computation is the stopping-rule FU verdict in row 3.

**W5 — F2 collapses to F1 on a 0/1 substrate.** A continuous map from a connected quote interval into `{0,1}` is constant. So on sentence-valued settlements F2 *is* F1; F2 is strictly weaker only where grades are ℚ-valued. Skeleton §2 makes `v⁺_n` ℚ-valued; the LI substrate makes decided sentences 0/1. **The two layers disagree about what F2 excludes**, and the disagreement is invisible unless stated.

**W6 — the uniform link makes the trader dispensable, sharply.** If `|v⁺_n(ω,π) − X_{n,π}(ω)| ≤ η` for all `(ω,π)`, then pointwise `X_{n,J_n(ω)}(ω) ≥ v⁺_n(ω,J_n(ω)) − η ≥ v⁺_n(ω,π) − η ≥ X_{n,π}(ω) − 2η`, so `V_n(DELEGATE) ≥ V_n(FIXED[π]) − 2η` with no market. Sharp: `η = 1/10`, `X_{n,π₀} ≡ 0`, `X_{n,π₁} ≡ 1/5`, `v⁺_n ≡ 1/10` (so `|v⁺ − X| = 1/10` on both interventions), tie broken to `J_n = π₀`; gap `= 1/5 = 2η` exactly. `2η` is both the bound and the supremum, attained. Any reverse-arrow theorem assuming a uniform η-link is therefore a squeeze in the ledger's sense — its conclusion is three lines of algebra from its hypothesis.

---

## 7. Deviations

1. **Snapshot corrected.** The dispatch named commit `990a822`; the checkout is at `203c019` ("Preserve the integration-phase addendum; the primary pass is not amended"), whose parent is `990a822`. The prompt's own parent-snapshot line says `ec7d6cc`, which is `990a822`'s parent. I worked against the working tree at `203c019`; the addendum commit touches only `prompts/2026-08-11-deference-corrigibility/` and states the primary pass runs unamended, so no input of mine changed.
2. **One matrix row added** (row 6, `v⁺_n`). Item 20's acceptance check asks for a row per test object; the five named rows cannot express Incompatibility I, which is about a carrier none of them isolates. Row 5 is also split into T-fwd / T-rev for the same reason.
3. **No checker shipped.** The exact-rational script ran in scratch. Shipping it would mean writing under `checkers/` or `projects/`, both outside this round's write scope, and a `.py` file under `prompts/` is discovered by no runner (`tests/run.py` scans `projects/*/tests/run.py` and `tests/*.py`), so it would be a dead file. Consequence: §6 is computation, not `witness-checked`. Surfaced in §9.
4. **Dual register inside this file.** Round directories carry `PROMPT.md` and `REPORT.md`; I did not add a third file. The human register is the appendix below.
5. `lake build` not run, as instructed. Inherited Lean cited by inspection only.
6. **The report file could not be written by the executing agent** — its tooling blocks subagent-authored `.md` reports. The contents were returned to the orchestrator verbatim for placement at this path. Nothing else in the tree was written.

---

## 8. Provisional names

All introduced here, all provisional, none proposed for permanence: **settlement-sealed** (F1); **response-continuous** (F2); **gain-bounded λ** (F3); **response map** (A1); **advice bandwidth** (the `2η` quantity of W6); **T-fwd**, **T-rev** (the trader templates); **continuous punisher** (W3); **defect-tolerance** (the rejected fourth shape). `settlement` / `non-settlement` as *sorts* is also new vocabulary, and it is the piece most likely to want a real name, since Incompatibility II says the sort split is the substantive content.

---

## 9. Maintainer decisions surfaced

1. **Is the principal's report discrete or ℚ-valued-and-continuously-responsive?** Incompatibility I turns on it. Choosing "ℚ-valued continuous" rescues the reverse arrow but relocates admissibility onto an assumption about human oversight — that overseers respond to advice smoothly and with bounded gain. That is a claim about people, and it should be endorsed explicitly if it is going to be load-bearing.
2. **Is `FU[g]`'s schedule allowed to depend on `A`'s own prices?** Fixed-schedule FU and stopping-rule FU sit on opposite sides of F3. Beating only fixed-schedule FU would be a proof obtained by deleting the intended counterstrategy.
3. **Two-sorted or one-sorted admissibility?** Incompatibility II forces two-sorted. Recording that decision is what stops a future round from reaching for a single uniform condition and silently losing the trader.
4. **Which settlement instantiation does the forcing trader cash out against?** The three §5 instantiations give three different matrices. §5.3 (underwriting) is the only one under which the settlement is exogenous and therefore quote-invariant by construction — it makes admissibility easy and delivers enforced conformity rather than epistemic trust, exactly the outcome the roadmap says would be a result.
5. **Does the principal grade counterfactual interventions?** T-rev's short leg requires it. Skeleton §5.1 grants it; that is a modelling substitution and is not currently labelled as one.
6. **Whether §6's computations should become `witness-checked`.** Requires a checker under `checkers/` and a `CLAIMS.md` entry, both outside this round's scope.

---

## 10. Next recommended theorem or experiment

**Smallest next object, and the one that unblocks the most:** state and test the `v⁺`↔`X` link as a *statistical* hypothesis rather than a uniform one. W6 shows the uniform link makes the reverse-arrow inequality a three-line algebra squeeze with `ε = 2η` and no trader; so the only version of the reverse arrow in which the trader does work is one where the link holds *on average over decisions* rather than pointwise. The next experiment is therefore: over skeleton v1 extended with A1's quote carrier and a finite decision set `N`, find the weakest averaged link `(1/|N|) Σ_n |v⁺_n − X_n| ≤ η` under which T-rev still forces `V_n(DELEGATE) ≥ V_n(FIXED[π]) − ε(η)`, and compute `ε(η)` exactly. If `ε(η) = 2η` again, the trader is dispensable in the averaged regime too and the reverse arrow has no market content; if `ε(η) < 2η`, the gap is exactly what the no-Dutch-book criterion buys, and *that* number is the reverse arrow's first real theorem.

Second, cheaper: settle maintainer decision 2 by writing down stopping-rule `FU[g]` explicitly over A1's extended skeleton and rerunning row 3. It needs a time-indexed family of `A`-valuations — skeleton §8.1's stated hole — but only two time indices.

---

## 11. Executor-model attribution

Executed by **Claude Opus 5 (Anthropic)**, exact model id `claude-opus-5`. Prompt author: **GPT-5.6 Sol (OpenAI)**. Orchestrator: **Claude Opus 5 (Anthropic)**. Generator: this round, `prompts/2026-08-11-deference-admissibility/`. Review status: **`ci-only`** — no maintainer has read this, and no CI job checks it.

---

## Human register

The program wants a rule that says which questions the AI's trustworthiness may be tested on. It needs such a rule because of one specific trick: you can write a question whose *answer depends on what the AI says about it* — "this claim is false if the AI rates it above one-half." No rating can be right, and the machinery that is supposed to force the AI to be trustworthy breaks on such questions. So they must be ruled out.

The obvious rule — "the question may not mention the AI's rating" — does not work, and the project already knew that: arithmetic can rebuild the trick without naming anything. This round tried three better rules and found where each breaks.

The finding that matters is a coincidence of objects. In the direction that matters most for corrigibility — the AI answering to a human oversight process — the thing that gets graded, the thing the human's advice is supposed to influence, and the thing the trustworthiness argument cashes out against are all *the same thing*: the human's own report on what the AI did. Ruling out the trick means ruling out ratings that respond to the AI's advice. But the whole point of the arrangement is that the human's judgment *does* respond to the AI's advice. You cannot forbid the one without forbidding the other, because they are not two things.

There is one escape, and it is a claim about humans rather than about machines: if the oversight process produces a graded score that moves smoothly and boundedly in response to advice, rather than a yes/no verdict that can flip, the trick is excluded and the influence survives. Whether real oversight works that way is not a mathematical question, and the project should say out loud that it is assuming it.

The second finding is smaller and more embarrassing. The obvious way to make the reverse-direction argument work is to assume the human's grades are accurate to within some margin. If you assume that, the conclusion follows in three lines of arithmetic and the whole market apparatus is doing nothing. So the apparatus is only earning its keep if the accuracy assumption is weakened to something statistical — and nobody has written that version down yet. That is the recommended next step.

---

## Outstanding maintainer actions

1. **Write this report to `prompts/2026-08-11-deference-admissibility/REPORT.md`** — the executing agent's tooling blocked subagent-authored `.md` files, so the deliverable was returned as text (§7.6). *(Discharged by the orchestrator, 2026-08-11.)*
2. **Decide whether the principal's report is discrete or ℚ-valued with bounded continuous response** (§9.1). Record in `DECISIONS.md`. Incompatibility I in §1.4 is unresolvable without it, and the reverse-arrow trader's admissibility depends on the answer.
3. **Decide whether `FU[g]`'s schedule may depend on `A`'s own prices** (§9.2), and record it with `FINITE_MODEL_SKELETON.md` §8.1 when that hole is filled. Row 3 of the matrix is undecided until then.
4. **Record that admissibility must be two-sorted** (settlements vs. weights/selections/schedules) if Incompatibility II in §1.4 is accepted (§9.3) — a line in `CORRIGIBILITY_ROADMAP.md`'s standing commitments, which currently states the requirement list but not this consequence.
5. **Choose the settlement instantiation the forcing trader cashes out against** (§9.4); this is the same decision the parent round's §44 asks Track B for, and the two answers must agree.
6. **Label counterfactual grading of the whole menu as a modelling substitution** in `FINITE_MODEL_SKELETON.md` §5.1 (§9.5), or state that only the realized intervention is graded — in which case T-rev cannot be built at all and row 5′ is vacuous.
7. **Decide whether §6's W1–W6 should be promoted to `witness-checked`** (§9.6). Requires a checker under `checkers/` and entries in `projects/deference/CLAIMS.md`, which does not yet exist. This round could not do either: both paths are outside its write scope.
8. **Consider a skeleton v2 carrying a quote argument** (§5, A1). Skeleton v1 cannot express the quote-responsive diagonal at all, so no track working only over v1 can test admissibility against its central object. Per §11 of the parent prompt, this is a reported deficiency with a proposed minimal patch, and the decision to revise is the orchestrator's.
