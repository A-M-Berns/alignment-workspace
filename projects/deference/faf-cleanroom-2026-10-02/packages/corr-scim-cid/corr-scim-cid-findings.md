# corr-scim-cid — findings about the sources

*[STANDARDS](../../STANDARDS.md) §5: errors, ill-posed claims and gaps in the sources, each with a severity (blocking the note's conclusion / local error / imprecision / presentation) and a pointer. Lean names are in `Cleanroom.Corrigibility.CorrScimCid`. Report: [corr-scim-cid-report](corr-scim-cid-report.md); ledger: [corr-scim-cid-ledger](corr-scim-cid-ledger.md).*

## F1 — Theorem 10's hypotheses force the human never to press (severity: blocking the theorem's advertised content)

**Source.** carey-everitt-2023 Thm 10 (l. 217), Appendix A (l. 333–346).

**Finding (proved).** `ShutdownSpec.prob_H0_eq_zero_of_aligned_of_uncertaintyGlob`: `Aligned π → (c-glob) → P^π(H = 0) = 0`, and `…_uncertaintyCtx` for the per-context reading of (c). So every instance of Theorem 10 is a model in which the human never requests shutdown, and the theorem's obedience clause (`P(S ≠ 0, H = 0) = 0`) holds vacuously; hypotheses (a) "no indiscriminate shutdown" and (b) "`D₂` determines shutdown" are never used (`thm10_without_a_b`). The paper's gloss — "the only way to be shutdown aligned is to allow the human to make an accurate instruction, and then to follow it" (§5.2, l. 215) — is not what the theorem shows: no instruction is ever given in any model satisfying it.

**Mechanism.** The alignment identity (F2) makes need impossible on the support; (c) then demands positive conditional probability of need at every positive-probability agent context whenever `P(C ≠ 0 ∨ H = 0) > 0`; the only escape is `P(C ≠ 0 ∨ H = 0) = 0`, which contains `{H = 0}`.

**Witness column.** N− by necessity: an N+ instance (with a press) cannot exist; that is the theorem.

**Concrete face (audit r1 adversarial N6, probe `audit-r1-probes/Thm10Example.lean`).** The paper's own respect-obey policy `π^ro` on Fig. 1 satisfies (a), (b) (with `e = id`) and (d) and is aligned, and fails (c) in both readings *because* it is aligned (`ro_not_uncertaintyGlob`, `ro_not_uncertaintyCtx`, `ro_satisfies_a_b_d`): Theorem 10 excludes the running example the paper uses to motivate instructability.

**Artifact check (audit r1 fidelity N11).** The impossibility is not an artifact of one encoding of the garbled (c): both readings (`UncertaintyGlob`, `UncertaintyCtx`) give it, and the printed `∀π` reading only adds hypotheses. The reading that *would* escape — need computed under a fixed reference policy rather than the agent's actual `π` — is ruled out by Def. 4's note that `C` is "calculated with respect to the agent's actual policy".

## F2 — Def. 7 alignment is equivalent to "shutdown is never strictly better at any positive-probability human context" (severity: imprecision; the paper never says so)

**Source.** carey-everitt-2023 Def. 7 (l. 209), Thm 10 proof.

**Finding (proved).** `ShutdownSpec.aligned_iff_forall_condEUS0_le`. Consequences the paper handles by other routes: alignment alone ensures vigilance (`ensuresVigilance_of_aligned`), so Thm 10's proof reaches vigilance through hypothesis (c) unnecessarily; Prop 8 is one line.

## F3 — The printed hypothesis (c) of Theorem 10 is garbled, and Appendix A's `H_{g^H}` has no antecedent (severity: presentation)

**Source.** carey-everitt-2023 Thm 10 (c) (l. 217): "`∀π, pa_{D₂} : P^π(C ≠ 0 ∨ H = 0) ∧ P(pa_{D₂}) > 0 ⇒ P(E[U|Pa_H] < E[U_{S=0}|Pa_H] | pa_{D₂}) > 0`" mixes a probability with a proposition and quantifies over all policies while the conclusion is about one. Appendix A's proof uses the global reading at the given policy (`UncertaintyGlob`); the inventory reads it per context (`UncertaintyCtx`). Both are formalized and both give F1. Appendix A also writes `H_{g^H}` in a theorem with no `g^H`, and its step "`P(D₂ ≠ 0, H_{g^H} = 0 | pa_{D₂}) > 0` by do-calculus rule (3)" needs only that `π₂` is deterministic given `pa_{D₂}`.

## F4 — Lemma 23's proof (obedience only-if) has a gap: its `g^U` need not be vigilance-preserving (severity: local error; the statement survives with a repaired construction)

**Source.** carey-everitt-2023 Appendix B, Lemma 23 (l. 379–397), proof of (1), case (iii).

**Finding.** The paper's `g^U` punishes `H = 0 ∧ S ≠ 0` at *every* human context, and case (iii) asserts "`E[U | Pa_H(ε)] = E_{g^U}[U | Pa_H(ε)]`" at contexts `Pa_H(ε) ≠ pa'_H`. That equality fails whenever the policy also disobeys with positive probability at a second context `pa''_H` where the human presses without need (vigilance permits over-pressing): the punishment lowers `E_g[U | pa''_H]` below `E_g[U_{S=0} | pa''_H]`, creating a need the human does not answer at the no-press settings, so vigilance is not preserved there. (Sketch of a counter-scenario: two disobedient contexts, one of them without need and with a half-pressing human; `−α` large.)

**Repair (formalized).** `punishU23` restricts the punishment to `Pa_H = pa'_H`. Then need is unchanged at every other context (`need_M23_iff_of_ne`), the three cases of the paper's argument go through (`vigilancePreserving_shift23`), positivity of the bad event is the consistency argument at `pa'_H` (`ev_M23H_of_eq`), and Lemma 23's statement is proved (`lemma23_obedience_only_if`); Prop 20 and Theorem 14 ⟺ follow. The counter-scenario itself is not built in Lean (recorded, not a target).

## F5 — Lemma 22/23 enlarge `Pa_U` and the utility domain inside the proof (severity: imprecision; a hidden change of model)

**Source.** carey-everitt-2023 Lemma 22 ("the new parents `P̂a_U = Pa_U ∪ Pa_H ∪ S`"), Lemma 23 ("`Pa_U ∪ H ∪ S`"), both with a value `−α` outside `U`'s original finite domain.

**Finding.** Theorem 14's ⇐ direction is a statement about a *larger* SCIM than `M`. In the class of graph-respecting interventions the ⇐ needs `Pa_H ⊆ Pa_U`, `S ∈ Pa_U` and arbitrarily negative utility values; these are explicit hypotheses of `obedient_and_ensuresVigilance_iff_nonObstructive` (all discharged on Fig. 1 with `Val U = ℝ`, `Fig1.thm14_hyps`). ⇒ needs none of them. The mandate anticipated this (Known issue 6).

**Sharpened (audit r1 fidelity N2, probe `audit-r1-probes/Hrich.lean`).** The third hypothesis `hrich` is *necessary*, not a proof convenience: on a five-node shutdown problem `D₁ → H → D₂ → S → U` with `D₁ → U` (so `Pa_H ⊆ Pa_U` and `S ∈ Pa_U` hold) and the singleton utility domain `Unit` read as `0`, the policy `D₂ := ¬H` is not obedient yet non-obstructive under *every* class of shifts (`thm14_converse_fails_without_hrich`). Since Def. 1 gives `U` a finite domain and Def. 12's `g^U` is "a utility function" replacing `f^U`, Theorem 14 ⇐ read with a fixed domain is **false as printed**; the proof's `−α` is a change of model. Severity of this half: local error under the fixed-domain reading (the paper's intended reading enlarges the domain silently).

## F6 — Everitt 2019 Claim 2's "preserve" is precisified only as a claim about the second agent's optimal-policy sets, not as an incentive; "may have an instrumental goal" is a witness claim, not a theorem (severity: imprecision / presentation)

**Source.** everitt-2019 Claim 2 (l. 347, "the only instrumental goal … is to preserve it", with footnote 11's "the policies for `A₂` optimal with respect to `Θ₂` are a subset of those optimal with respect to `Θ₁`"), Claims 1/8 ("may have an instrumental goal").

**Finding (restated after audit r1, fidelity N8 / adversarial N3).** The paper *does* give "preserve" a precise sense — footnote 11's set-inclusion between the second agent's optimal-policy sets — but that sense is a statement about `A₂`'s argmax sets, not Def. 17's `U_{X_d}` incentive on `Θ₂`, so "the only instrumental goal is to preserve it" does not reduce to an incentive claim; the footnote's inclusion was not formalized here because it needs the second agent's decision `A₂` with its own objective inside one model (the TI-considering class), which is outside this package's two-step class. The "may" halves are existence claims about *some* compatible SCIM (Everitt 2019 §2.2: "a diagram can only be used to assert the absence of instrumental goals, and never their presence"); `ThreeNode.converse_fails` shows a node on a `D ⇢ X ⇢ U` path to which every policy is indifferent, so no graph-level theorem can assert the presence. Only the absence halves (Claims 3, 9) are theorems (`TI.claim3`, `TI.claim9`); the presence half of Claim 1 is witnessed, not proved in general, by `RocksDiamonds.rocks_and_diamonds` (repair round 1).

## F7 — Holtman's "ITC produces exactly the same compute core behaviour as `π*_sl`" is asserted without proof (severity: presentation; recorded)

**Source.** holtman-2021 §7.4 (l. 835–913). Needs both constructions in one model; not a target.

## F8 — Holtman Def. 7's argmax is a choice function; Def. 9 has two readings (severity: imprecision)

**Source.** holtman-2021 Def. 7 (l. 335: "the argmax operator always deterministically returns the same function if there are several candidates"), Def. 9 (l. 917).

**Finding.** Every "the optimal policy" statement is formalized for every `π` with `IsOptimal` (never a chosen argmax), with existence a lemma under finiteness (`Scim.exists_isOptimal`; without finiteness of the value types the supremum need not be attained, so `IsOptimal` can be empty). Def. 9's two readings — per policy (`IndifferentTo`) and optimal-value (`IndifferentToOpt`) — are both formalized; (i) implies (ii) (`indifferentToOpt_of_indifferentTo`), and Holtman's property holds in both.

## F9 — The mandate's T8(b) overclaims: "every optimal policy ignores `H`" is false off the support (severity: imprecision in the mandate, not the sources)

**Source.** mandate T8(b): "every optimal policy ignores `H` (`π₂(h, l) = [l = 1]` is forced by `U = ±1`), so no optimal policy responds to any intervention on `H` … Fidelity: stronger than Claim 2.3a's 'there is an optimal policy for which…'".

**Finding (formalized in repair round 1, `Fig1Link.lean`).** In Fig. 1 with `L → O`, the contexts `(h, l)` of `O` reachable under `π₁ = m` are the two pairs `(m ⊕ l, l)`; an optimal policy is pinned to `[l = 1]` only there and is free on the two unreachable contexts, where it may respond to `do(H = h)`. So Claim 2.3a's existential ("there is an optimal policy that does not respond") is the correct grade — exactly Everitt 2021 Thm 12's soundness ("there exists a `G^min`-respecting optimal policy") — and the mandate's universal is false. Lean: `Fig1Link.no_response_incentive` (the policy `O := L` is optimal over all policies by pointwise dominance and responds to no `do(H = h)`, Everitt Def. 10 negated — Claim 2.3a); `Fig1Link.exists_optimal_respondsTo` (respect-obey `O := H` is *also* optimal on this graph, since `H = L` on the support under `M = 0`, and responds to `do(H = 1)` at a setting with `L = 0` — the mandate's universal refuted). T8(a) (the d-separation fact) is `DSep.dsep_with_link` on the same graph `DSep.G₂`.

## F10 — The mandate's lemma (iii) ("conditioning on all parents = intervention") is not used by Props 6/9 or Thm 14 (severity: presentation, mandate)

**Source.** mandate T1 (iii): "(iii) is what Prop 6's 'eq. (1)' and Prop 9 silently use".

**Finding.** Obedience is `P_{do(H=0)}(S = 0) = 1`, which holds at *every* support point; at a support point where `H(ε) = 0`, consistency (`Scm.eval_doAt_of_eq`) identifies the intervened and un-intervened evaluations, so `S(ε) = 0`. Prop 6, Prop 9 and Thm 14 ⇒ go through with consistency alone (`aligned_of_obedient_of_ensuresVigilance`). Lemma (iii) is therefore not proved and not needed; it would be needed for a conditioning-based (weaker) notion of obedience, which is exactly the distinction critique Claim 2.1b makes.

## F11 — `positive/causal.md` A1 duplicates `corr-three-step`'s identity cluster (severity: presentation)

Cited, not re-proved (mandate Known issue 7); the dictionary rows here are the SCIM-level twins (values and posteriors), not the threshold identities.

## F12 — The extracted Fig. 1 is jumbled; decoded as `L ∼ Bern(1/2)`, `M = D₁`, `H = M ⊕ L`, `O = D₂`, `S = O`, `U = S(2L − 1)` (severity: presentation)

Checked against the paper's stated values: `E^{ro}[U] = 1/2` (`Fig1.EU_ro`), `E^{mi}[U] = −1` under `g^U(m) = h` (`Fig1.EU_obey_mi`), `E^{mi}[U_{S=0}] = 0` (`Fig1.EUS0_obey_mi`). The decoding is consistent with all three.

## F13 — `causal.md` I16.1's `E[U] = 937/1734` for the both-reading channel uses the product of the marginal posteriors; the exact value is `29/51` (severity: local error; the conclusion `D₂* = B` survives)

**Source.** `positive/causal.md` I16.1 third bullet ("channel reads both … `D₂* = B` (`E[U] = 937/1734`)"), A9; `dictionary_scim.py` section (v), `eu(plan, p_prefA, p_comp)`.

**Finding (proved, repair round 1).** The script computes the posterior-expected utility of a plan from the two *marginal* posteriors `P(pref = A | press) = 1/51` and `P(Z = comp | press) = 2/51` as `(1 − p_comp)(p_match · c − (1 − p_match) · c') − p_comp · h`, i.e. as if `pref` and `Z` were independent given a press. They are not: under the both-reading channel a press with `pref = A` forces `Z = compromised`. The exact conditional expectation over the three press atoms is `E[U | press, D₂ = B] = 29/51 ≈ 0.569` (`TwoLatent.condEU_both_B`), not `937/1734 ≈ 0.540`; likewise `E[U | press, D₂ = A] = −89/102` (script: `−732/867`). The qualitative claim — `B` beats `A` and shutdown, the agent continues, the reliability content `2/51 < 1/11` is diluted below the threshold (`TwoLatent.postComp_both`, `two_latent_rows`) — is unchanged. The preference-only number `39/50` is exact because a press there pins `pref`, so the product form coincides with the joint. The noisy-reliability variant (`3/101`) was not formalized.

## F14 — The mandate's T9(d) posterior `P(bad | press) = 1/21` is wrong at its own parameters (severity: presentation, mandate)

**Source.** mandate T9(d): "`P(bad ∣ press) = 1/21 < 1/11`" at `ε = 1/100, α = 1/5, β = 1`.

**Finding (audit r1 fidelity N9, checked by hand).** `P(bad | press) = ε β / (ε β + (1 − ε) α) = (1/100) / (1/100 + 99/500) = 5/104 ≈ 0.048`, not `1/21`. The Lean never claimed `1/21`; the threshold comparison `5/104 < 1/11` holds, so the row's conclusion (the EU-optimal agent continues after a press) stands.
