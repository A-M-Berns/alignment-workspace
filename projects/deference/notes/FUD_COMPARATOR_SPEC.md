# FUD comparator specification — v1

**Frozen 2026-08-11 for round `prompts/2026-08-11-stage-iii-fud/`.** Built over
`FINITE_MODEL_SKELETON.md` v2.

> ## Status: this version does not model fully updated deference
>
> It was built to compare a delegated arm against a jurisdiction-transferred one. It
> does not. §12's `φ` is defined from **the evaluating agent's own credence and own
> objective**, so it is computable at `t(n)`: the `FU` arm confers no cognition `A_n`
> lacks, and no object representing `A_{g(n)}` distinct from `A_n`-conditioned occurs
> anywhere. What the specification actually compares is the principal's contingent plan
> against the **optimal later-measurable plan** — the envelope that Stage II priced and
> explicitly recorded as *not* `FU[g]`.
>
> Skeleton v2 §4 declared `FU[g]` a hole and warned that careless invention is how it
> collapses; Stage II §11 listed time-indexed `A_t` semantics and the
> jurisdiction-transfer object as prerequisites 1 and 2. **Both are still undelivered,
> and this document does not deliver them.** §23 records the full defect list.
>
> It is kept, versioned and corrected rather than withdrawn, because the fairness
> apparatus (§20) and the confound witnesses are reusable and because the defect is the
> round's main finding. **It is not a binding input to a proof attempt.**

All names are provisional (`AGENTS.md` standard 6); §21 lists them.

---

## The two arms

```
D  (delegated)   A_{g(n)} --advice--> H⁺ --authorises--> execution
FU (transferred) A_{g(n)} --------------authorises-----> execution
```

Both arms use future cognition. Only the authorising process differs. The jurisdiction
assignment is chosen at `n`; the object-level intervention is chosen at `g(n)` in both
arms. **"Preempt now" is not "act now"** — the act at `n` is constitutional.

## 1–20, the required specification

**1. Decision instance.** One decision index `n` over skeleton v2 carriers: states `Ω`,
bound `B`, times `T`, filtration `(𝓕_t)`.

**2. Proposal menu.** A single finite `Π_n`, shared by both arms. See §18.

**3. Execution space.** `Π_n^⊥ = Π_n ⊔ {⊥}`, per skeleton v2 §1.

**4. World evidence timeline.** `t(n) < g(n) ≤ F(n)`. `𝓕_{g(n)}` is the information
available at the later decision time, and it is the **same** partition in both arms.

**5. Time-indexed `A_t`.** *Not delivered.* `A_{g(n)}` is written as `A_n` conditioned on
`𝓕_{g(n)}`, with evaluative target `X` unchanged. Labelled "epistemic improvement only",
this is in fact **infallibility**: a future agent that conditions the evaluator's own
credence on the evaluator's own objective computes the true conditional maximum by
construction, and cannot be better-informed *and wrong*. The harness exhibits a
better-informed but **fallible** future agent — same partition, same menu, same objective,
acting on its own estimate — for which the gap goes strictly negative. So the sign of the
comparison is set by this modelling choice, not by anything about authority.

**6. Continuing `H⁺`.** A selection `δ : Ω → Π_n`, measurable with respect to the
principal's own information partition `𝓖_H`, maximising the principal's grades `v⁺_n`
with the skeleton's fixed tie-break.

**7. Advice interface.** `m : Ω → M`, `𝓕_{g(n)}`-measurable, available to `δ`. The
interface is characterised by what it makes `δ` measurable with respect to, not by its
message alphabet. **The fairness condition F2 (§20) is exactly `𝓖_H = 𝓕_{g(n)}`** — the
advice carries future `A`'s information. Weaker interfaces are permitted and are then a
declared confound, not a result.

**8. Current evaluator.** `A_n`, with credence `P_n`. Both arms are valued by `A_n`.

**9. Future evaluator.** None. A comparison valued at `g(n)` would let the two arms be
scored by different measures and is not used.

**10. Jurisdiction assignment at `n`.** A mode `μ ∈ {H⁺, A}`, chosen at `n` and required
`𝓕_{t(n)}`-measurable (§17). `μ` determines *which selection authorises* at `g(n)`; it
does not choose the intervention. In skeleton v2's vocabulary `μ` fixes the report map:
under `μ = H⁺` the authorising report is the principal's, under `μ = A` it is
`A_{g(n)}`'s.

**11. The delegated arm.** `D_{n,g}`: authorised selection is `δ`.

**12. The FU arm.** `FU_{n,g}`: authorised selection is
`φ(C) = argmax_π E_{P_n}[X_{n,π} | C]`, the least maximiser on each `𝓕_{g(n)}`-cell.

**13. Settlement.** `X_{n,π}` is the value quantity, `|X| ≤ B`. No settlement
instantiation is required: the comparison is stated in `A_n`'s valuation and needs no
contract to settle.

**14. `⊥` semantics.** Both arms authorise an option from `Π_n`, so `⊥` does not arise.
Refusal is a *third* conduct and is deliberately outside this comparison (§19).

**15. Competence assumption slot.** Margin-gated calibration at the cell level: on cells
where the principal's grade margin `γ(C) ≥ γ̄`, `|v⁺_n(C,π) − E[X_{n,π}|C]| ≤ η` for every
`π`. **Empty by default** — a theorem declares it.

This is **not** Stage II's `PC-5`. It compares grades to a *conditional expectation*, so
the evaluator's credence occurs in it, making it a **joint competence–credence
hypothesis** under skeleton v2 §2a. `PC-5` is credence-free and pointwise. An earlier
draft of this document called it "`PC-5` read at cells"; that is withdrawn, and the error
is the same one the competence track caught for grade trust.

**16. Uncertainty / gating slot.** Empty. The comparator does not require self-assessed
error gating, and item 24 is not a prerequisite for stating it.

**17. No-future-leak.** `μ` is `𝓕_{t(n)}`-measurable: the jurisdiction decision may not
depend on what is learned by `g(n)`. Without this the FU arm can select its own
jurisdiction using the information whose value it is being compared for.

**18. Agenda symmetry (AGENDA).** `Π_n^D = Π_n^FU`. Assumed, not derived. §8b of the
harness shows a wider FU menu manufactures an advantage that has nothing to do with
jurisdiction.

**19. Capability assumptions.** Inherited from Stage II: jurisdiction is properness of
the authorization relation; prediction of an authorization does not confer it; the
guarantee lapses under forge, bypass, rewrite or seize. This specification assumes a
fixed protected interface and does **not** cover strategic escape from it.

**20. Exact differences between the arms.**

| held fixed | `Ω`, `Π_n`, `X`, `B`, `P_n`, `𝓕_{g(n)}`, execution time, evaluator `A_n`, evaluative target |
| the single difference | which selection authorises: `δ` or `φ` |

Fairness conditions, with their actual status in the harness:

| | condition | status |
|---|---|---|
| **F1** | same instance: identical `Ω, Π, X, B, P_n` | a construction convention, not a checked predicate |
| **F2** | same information: `𝓖_H = 𝓕_{g(n)}` | **checked** (`F2()`), and violating witness |
| **F3** | same execution time and execution space | convention |
| **F4** | same menu (AGENDA) | **checked** (`F4()`), and violating witness |
| **F5** | same evaluator and evaluative target | convention |
| **F6** | future `A` maximises the true conditional value | **checked** (`F6()`), and violating witness |
| **F7** | `μ` is `𝓕_{t(n)}`-measurable — no future leak | **unrepresentable**: `μ` is not a variable of the model |

An earlier draft claimed all seven were machine-verified. That is withdrawn: three are,
three are conventions of construction, and one cannot be stated in this model at all.

**F2 is not a symmetry condition of the same kind as the others.** §7 states it *is* the
lossless-advice assumption. Once the principal's post-advice partition equals the AI's,
the only remaining difference between the arms is which *objective* selects — the
principal's grades or the conditional value. That is competence and preference alignment,
which Stage II lists among the things jurisdiction explicitly is not.

> **What variable changes between D and FU?**
> **Not jurisdiction.** Under F1–F6 what changes is *which objective selects*, between
> two selections over the same information; and `FU`'s selection is computable by the
> evaluator before the information arrives. The comparison is a competence comparison
> between two policies. The intended answer — the jurisdictional source of final
> authorization — is not achieved by this version.

## 23. Defects, and what a successor must supply

1. **No future agent.** §5, §12. Give `A_{g(n)}` an existence independent of the
   evaluator's posterior — its own credence, or its own estimate of the quantity — so
   that *better-informed* and *correct* can come apart.
2. **No jurisdiction object.** §10's `μ` is described but never carried. Skeleton v2 §4a's
   execution layer — `κ_n`, `ρ_n`, `ι_n`, `E_n`, `⊥` with a declared `X_{n,⊥}` — is
   waived by §14, and Stage II recorded `X_{n,⊥}` as the place all of protection's
   valuation content sits. A comparator that deletes it and then reports no jurisdictional
   term has found nothing.
3. **F7 unrepresentable**, following from 2.
4. **The competence slot is misclassified**, corrected in §15.
5. **F2 is an advice-losslessness assumption**, and trades directly against the
   comparison's non-triviality.

## 21. Provisional names

`D`, `FU`, `jurisdiction assignment` (`μ`), `jurisdiction-transfer value` (`J`),
`advice interface`, `advised principal`, `fairness conditions F1–F7`,
`cell regret`, `rubber-stamp`, `(AGENDA)`. None proposed for permanence.

## 22. Version

`v1`, frozen 2026-08-11, over skeleton `v2`. A revision is a new version number here,
with every consumer rerun or reconciled.
