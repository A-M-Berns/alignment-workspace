# `bli-rvc-ui` — findings about the sources

Findings about the research ([STANDARDS](../../STANDARDS.md) §5), each with a severity (blocking / local error / imprecision / presentation) and a pointer. Every "the author meant" sentence is ATTRIBUTION-UNVETTED. Refutations proved in Lean name the declaration (namespace `Cleanroom.Bli.BliRvcUi`). The mandate's eleven expected items are F-1…F-11; F-12 onward are new; F-19 and the second halves of F-2, F-6 and F-7 were added in repair round 1 (2026-09-30) after audit round 1.

## F-1 — `main.tex:349`: "real-value coherence" has no definition; "large random variables" undefined (presentation)

- Pointer: `main.tex:349–350` ("beliefs about random variables should cohere appropriately, so that for example, the computationally uncertain expectation of random variables $A$ and $B$ sums to the expectation of $A+B$"); bli-paper-048's flag.
- Finding: the sentence names one example (additivity of expectations) and no definition; "large" is never defined for random variables. The five candidates are the Extra Notes' A–E (bli-slides-014). This package formalizes (B) as `RVC_B` (T2: a finite mixture of point values on the thresholds, equivalent to two-axiom coherence on the threshold algebra relative to the monotonicity and range facts, `rvcB_iff_twoAxiom`) and (E) as `RVC_E_exact` / `RVC_E_eps` on FAF's grid expectation (T1). (C)/(D) — the joint of two variables — is stretch S1, not attempted.
- Severity: presentation.

## F-2 — Extra Notes p. 7: "some versions of D, E follow directly from propositional coherence" (imprecision)

- Pointer: `AISC 2025 - Extra Notes (BLI and real-value coherence).pdf`.pdf) p. 7, the annotation on (D), (E); bli-slides-014's flag.
- Finding, both halves (the second added in repair round 1, audit r1 (b)): **for the exact expectation of a world marginal the annotation is right** — over any finite mixture of worlds valuing `Z = X + Y`, the mixture mean `∑ wᵢ xᵢ` is exactly additive (the identity `hsplit` inside `rvcE_eps_of_worldMixture`'s proof is that statement). **For the paper's grid estimator `E_n` (FAF's `expectApprox`, a Riemann sum at precision `k`) it holds only at ε**: additive to within `3/k` (`rvcE_eps_of_worldMixture`, `rvcE_eps_of_coherentOn` relative to a stage), and **exact** additivity fails at every finite precision even at a *single* world valuing `Z = X + Y` (`rvcE_exact_fails`: `𝔼ᵏ(X) + 𝔼ᵏ(Y) = 2/k ≠ 1/k = 𝔼ᵏ(Z)` for the world holding `X.gt r ↔ r < 1/(2k)`, `Z.gt r ↔ r < 1/k`). So the "impossibility" of T1.1 is, by design, an artifact of the estimator's grid — the failure is the grid, not incoherence — and the imprecision is about the paper's own `E_n`, not the idea. For (D) the annotation presupposes (C)'s language (product cells) — S1, not formalized here. In the limit (E) is FAF's linearity of expectation (`rvcE_limit`, hypotheses (b)).
- Severity: imprecision (about the estimator at finite precision; correct for the exact expectation).

## F-3 — Extra Notes p. 5: "independent & uniform" for unmentioned real variables is coordinate-dependent (imprecision)

- Pointer: p. 5 ("we might assume any real-valued variable not mentioned by small beliefs to be independent & uniform"); bli-slides-012's flag.
- Finding: uniform on `x` is not uniform on `x²`, so the default is not reparametrization-invariant, unlike the 50–50 propositional default (which is invariant under negation, the only "reparametrization" of a proposition). No theorem; a note.
- Severity: imprecision.

## F-4 — bli-paper-2-026: the AI-written "LUV coherence" clause 3 is two-sided and unsatisfiable (local error in AI text; refuted)

- Pointer: Phase 2.1's "Definition (LUV Coherence)", clause 3 (`|P_n(∀x.φ(x)) − P_n(φ(t))| → 0`).
- Finding: `twoSided_ui_unsat` — the clause forces every pair of instances to have asymptotically equal prices, so one instance priced `→ 1` and one `→ 0` refute it; `twoSided_ui_unsat_paper` exhibits this over every inductor over `paperDP T` with the T4.6 table facts as instances (the actual table's literal `→ 1`, the flipped table's `→ 0`). The one-sided `UILimit` is the definition of record and is a theorem (F-6).
- Severity: local error (in AI text); kept out of every definition.

## F-5 — bli-soto-a-054: "that trader with trades in inconsistent worlds eliminated would also exploit it" (imprecision)

- Pointer: Soto PDF 07 p. 1, Step 1.
- Finding: the one-liner ignores that eliminating trades changes the trader's e.c. certificate and its cash flows. Over FAF no such argument is needed: `AxProcess F` is a computable deductive process (`axProcess_computable`), its union with a computable base is computable (`union_ax_computable`), and FAF's `LIA_is_logical_inductor` gives an inductor over the union (`lia_union_ax_isLI`, T3.2), whose plausible worlds all satisfy the schema instances. Soto's "Universal Inductor" additionally forces exact price `0` on `Ax`-inconsistent finite worlds at every finite day — that exactness is what FAF does not give (and what `bli-superbelief` E7 shows the LIA does not have).
- Severity: imprecision (the conclusion survives in FAF's form; the argument does not).

## F-6 — Over a theory, Soto's Step 1 is redundant; PDF 07's second limit inequality fails (local error; refuted)

- Pointer: Soto PDF 07 p. 2 ("`Ax` ensures `P(∀mφ(m)) ≤ lim_m P(⋀φ(i))`. We also get the other inequality … because `lim_m P(¬∀mφ(m) ∧ ⋀_m φ(i)) = 0`. Indeed, the latter could only fail if a finite and `Ax`-consistent `C ∧ ¬∀mφ(m)` propositionally entailed infinitely many `φ(i)`. This isn't possible with our `Ax`, because the only way to have this is through quantification"); bli-soto-a-2-006; bli-soto-a-082.
- Finding, first inequality: over `paperDP T` universal instantiation in the limit is a theorem of the criterion **without any schema process** (`ui_limit_paperDP`, T3.6): `T ⊢ ∀⁰ φ 🡒 φ/[‘↑c’]` is logic (Foundation's `specialize`), `paperTheoryDP` publishes its prime decomposition, and `holds_paperPrimeDecompose_imp` makes it `u 🡒 inst c` in every completed world. `AxProcess` matters only for a base that does not prove logical theorems (a finite `Q`, a bare propositional process) — `bli-extrapolation`'s setting.
- Finding, second inequality: refuted at the criterion level, by two mechanisms that repair round 1 separated (audit r1, both lenses). **(i) The sibling prime, with undecided instances** — `secondLimit_fails_free` / `secondLimit_fails_free_paper` (T3.7 (b), `Ui/Free.lean`): universal-role atom `u`, a sibling `u'` (playing `∀m(φ ∧ φ)`: syntactically distinct, same instances), **free instance atoms** that no base decides (`free2_inst_lt_one`: every `P∞(inst c) < 1`), and schema implications for both. The world "`u` false, `u'` true, all instances true" is consistent with every stage, so by non-dogmatism `P∞(∼u ⋏ ⋀_{i≤m} inst i) ≥ P∞(∼u ⋏ u') > 0` **uniformly in `m`**. Here `u'` is the only sentence of the process entailing every instance, so Soto's stated reason is wrong as stated: `∼u ⋏ u'` is a finite `Ax`-consistent conjunction entailing every instance, through the sibling prime rather than through quantification. **(ii) The theory, with theorem instances** — `secondLimit_fails_ax` (over `paperDP T ∪ Ax(u) ∪ Ax(u')` with instances `trueInst T`, theorems of `T`): the same bound, but the sibling is inert (`⊤` entails the instances; the bound holds over `paperAx T` with no `u'` — audit r1 probes `SiblingIdle`, `SiblingFreePaper`). This is the semantic reason: over a theory the instances are entailed by the theory, not by any finite `Ax`-consistent conjunction, and `u` stays undecided. Semantically (over `paperDP T`) the second inequality is Gödel: a true unprovable `Π₁` universal stays `< 1` while every instance `→ 1` — the fresh-atom form is `ui_strict_fresh` (T3.5, N−: the universal role there is nominal, F-19); the `paperUI` form is `ui_strict_paper_open` (OPEN; Foundation's Gödel II is importable, the plumbing is not done).
- Whether Foundation's NNF collapses `¬¬φ` to `φ` (which would make Soto's literal `¬¬φ` variant coincide with `φ`) was **not** probed; the witnesses use a fresh sibling atom, which needs no such fact.
- Not shown: that without the sibling and with undecided instances the bound can *fail* for some inductor (that needs an inductor with a prescribed limit; the limiting belief is only finitely additive, so nothing forces `P∞(∼u ⋏ ⋀_{i≤m} inst i) → 0` either).
- Severity: local error (the second inequality and its reason); the first inequality is a theorem for stronger reasons than given.

## F-7 — `bli-program-desiderata` P8: "exact UI at finite day is *equivalent* to `FiniteCoherent`" is one-directional in general (imprecision in the program)

- Pointer: P8's statement ("exact UI at finite day `n` is *equivalent* to `FiniteCoherent (Q n) _ ((DP.union AxProcess).D n)` on the relevant sentences").
- Finding: the direction the desiderata need holds — coherence relative to a stage containing `u 🡒 inst c` gives `V u ≤ V (inst c)` (`uiAt_of_coherentOn`, T3.4, `Ui/Finite.lean`). The converse fails when instances share primes: with `inst 0 = p`, `inst 1 = ∼p`, `V u = 0`, `V p = V (∼p) = 1`, `UIAt` holds and `V` is not `CoherentOn` relative to any stage on any atom set containing `p` (`uiAt_not_coherent_shared`: the two instances cannot both be priced `1` by a mixture of worlds, since `payout p + payout (∼p) = 1` in every world). That `V` is incoherent on its own, so it refutes only the literal reading of P8 (audit r1 N1/(a)). **The converse also fails on pairwise distinct atoms for a base-coherent `V`** (repair round 1, `uiAt_not_coherent_baseCoherent`): the uniform mixture `uniformFour` of the four worlds on `u = atom 1`, `inst = atom 0` is `CoherentOn ∅ A` for every `A`, satisfies `UIAt` at `{0}` (`½ ≤ ½`), and is not `CoherentOn {u 🡒 inst} {0,1}` — augmented-stage coherence forces `V (u ⋏ ∼inst) = 0` while here it is `¼` — although that stage is coherently inhabited (`pairUI_aug_coherent`). So among coherent valuations, augmented-stage coherence is strictly stronger than exact UI, and the true converse is `coherentOn_of_uiAt_atoms` in its "extends to a coherent `V'`" shape (mass `V u` on the all-true world, the rest on `u`-false worlds with independent instance marginals `(V (inst c) − V u)/(1 − V u)`, the product mixture over `C.powerset`), not a literal iff (F-13). All four are proved in Lean.
- Severity: imprecision.

## F-8 — bli-soto-a-055 / bli-soto-a-2-008: the decidability sketch for `Ax`-entailment is wrong as stated (imprecision; recorded, owned jointly with `bli-extrapolation`)

- Pointer: PDF 07 p. 2 ("from a set of prime formulas `Ax` can only derive smaller or equal length prime formulas … we can syntactically cap the length of a possible proof").
- Finding: instances with long numerals are *longer* than the universal; the cap needs the fresh-numeral lemma (Lemma A of bli-soto-a-2-008). Stretch S4, not attempted here; `bli-extrapolation` needs it for a computable definition of record.
- Severity: imprecision.

## F-9 — bli-soto-a-076 / bli-soto-b-2-007: "all summary statistics are LUVs" is ill-posed as stated (imprecision)

- Pointer: the Sep-18 email before the `//////` mark.
- Finding: which statistics of a joint over finitely many binary variables and a bounded `U` are LUVs, and that their expectations determine the joint, is a precise finite claim (S5) that the source does not state; S5 was not attempted. Recorded.
- Severity: imprecision.

## F-10 — bli-soto-b-2-013 (anti-universal traders): an open question, not a target

- Pointer: the "devices against false universals" proposal.
- Finding: a trader against a *true* unprovable universal is never paid and keeps its price low forever (the T3.5 world: `u` can be false at every stage), so the device trades false-universal harm for true-universal harm; a modified market would need `corr-exo-trader`'s exogenous demand. OPEN question; no theorem.
- Severity: —.

## F-11 — bli-soto-b-2-005: the universal policy-point belief is object-level (presentation)

- Pointer: Soto's objection (ll. 230–231) and the author's retraction (ll. 270–272).
- Finding: `∀Q (P(Q) ∧ (𝑸_m = Q → A_m = a) → ↑U)` quantifies over states and LUV values only; encode it as a sentence over state/policy atoms (`bli-found`'s `stateAtom`/`policyPoint`/`actionAt`), never as a quotation of `ℙ`'s expectation. The extension (a `UIFamily` over those atoms with T3.3 applied) was not attempted.
- Severity: presentation.

## F-12 — Mandate design decision 2: `ValuesAt` does *not* force the range fact at threshold `1` (local error in the mandate; corrected in the definitions)

- Pointer: mandate §2, decision 2 ("`rangeFacts X R := {X.gt r | r < 0} ∪ {∼X.gt r | 1 ≤ r}` (a `[0,1]`-LUV: `ValuesAt` forces both)"); FAF `PCWorld.ValuesAt` (`Framework/Expectations.lean:376`).
- Finding: FAF's cut semantics decides `X.gt r` only for `r < x` and `x < r`; at `r = x` it says nothing. A world valuing `X` at exactly `1` need not hold `∼X.gt 1`. So `holds_rangeFacts_of_valuesAt` carries `1 ∉ R`, and the limit form of (B) (`rvcB_limit`, `rvcB_limit_lia`, T2.3) is stated for threshold sets avoiding `1`. Nothing else changes: the two-axiom equivalence (T2.1) is unconditional because `RVC_B` itself forces `V (X.gt 1) = 0` (point values lie in `[0,1]`, indicator `r < x`), consistent with the `1 ≤ r` range fact. Symmetric agnosticism at `r = 0` is harmless (no range fact there; `RVC_B` leaves `V (X.gt 0)` free in `[0,1]`).
- Consequence for dependents: any theorem about quote LUVs at the exact threshold `1` (or a threshold equal to the quoted value) must not assume the world decides it; `bli-found`'s `le_of_holds_quoteAt` already respects this.
- Severity: local error (in the mandate's gloss, not in any source); the definitions of record are unaffected.

## F-13 — Mandate T2.1 and T3.4: "iff" statements between a threshold/atom profile and coherence must be "extends to" (imprecision in the mandate)

- Pointer: mandate T2.1 (`rvcB_iff_twoAxiom : TwoAxiomCoherent V … ↔ RVC_B V X R`), T3.4 (`coherentOn_of_uiAt_atoms`).
- Finding: `RVC_B` and `UIAt` constrain `V` on the threshold/instance atoms only, while `TwoAxiomCoherent` / `CoherentOn` constrain the whole generated algebra (or every sentence with atoms in `A`). A literal iff is false (take `V` right on the atoms and garbage on a compound). The statements of record are "there is a `V'` agreeing with `V` on the atoms that is coherent" (`rvcB_iff_twoAxiom`, `coherentOn_of_uiAt_atoms`), the shape `bli-finite`'s `coherentOn_iff_twoAxiom` already has; the one-way direction from coherence needs no such clause (`rvcB_of_twoAxiom`, `uiAt_of_coherentOn`).
- Severity: imprecision (mandate).

## F-14 — Mandate T3.5: the instance family `paperPrimeDecompose ψ_c` has no e.c. certificate in FAF; quotation literals do (imprecision in the mandate; design substitution disclosed)

- Pointer: mandate T3.5 ("`F.inst c := paperPrimeDecompose ψ_c` with each `ψ_c` `T`-provable"), T3.3 (`hec` "discharged for the witness families from the `MachineSentenceCodes` constructors").
- Finding: `lic_provind_true` needs `MachineSentenceCodes` of the instance family; for prime decompositions of sentences with a growing numeral FAF provides no constructor. FAF's quotation package does: a `BooleanQuoteCode` of a total decider has `sentence_poly`, each literal is `T`-provable (Σ₁-completeness, `pos_complete`) and process-published (`quote_positive_enters`). The witnesses use `trueInst T c := ⌜True(c)⌝` (`Ui/Paper.lean`), which is "each instance provable" in the form the process actually publishes. The paper-facing family `paperUI φ` is used where no certificate is needed (T3.6, through semantic monotonicity of the limiting belief, which only needs `MachineSentenceCodes.const`).
- Severity: imprecision (mandate); no source claim affected.

## F-15 — Mandate T3.2/T3.5: fresh-atom family `7` is no longer free (registry drift)

- Pointer: mandate §0 ("families `7`–`15` are reserved/free … use families `7` (UI universal atoms) and `8`"); `bli-found` `Tags.lean` registry (family `7` = overlay-witness atoms, owner `bli-transfer`, payload `Nat.pair day rest`).
- Finding: `bli-transfer` took family `7` after the mandate was written; its day-`0` payloads could coincide with this package's `⟨0, 0⟩`. Nothing logical follows (the two packages never share a process in one theorem), but the registry exists to prevent exactly this. This package's universal-role atoms use family **`9`** (payloads `⟨0, 0⟩`, `⟨0, 1⟩`, `⟨0, 2⟩`); the RVC witness thresholds use family `8` as mandated. **Orchestrator: add rows `9` (UI universal atoms, `bli-rvc-ui`) and `8` (RVC witness thresholds, payload `⟨0, ⟨j, encode r⟩⟩`, `bli-rvc-ui`) to `Tags.lean`.**
- Severity: presentation (registry).

## F-16 — Mandate T4.6: `M ⟨q, c⟩ := entry / d` is not `[0,1]`-valued on illegitimate codes (imprecision in the mandate)

- Pointer: mandate design decision 6 ("`M ⟨q, c⟩ := ((entryOf c (tableOfCode q)).getD 0 : ℚ) / d`").
- Finding: `RationalQuoteCode` requires `∀ z, 0 ≤ M z ∧ M z ≤ 1`, and a table code listing an index above `d` violates it. The reading of record `tableEntryValue c d q` clamps at `1` when the entry exceeds `d` (and reads `0` at `d = 0`, `mkRat`'s junk value); on legitimate codes it is `entry / d` as intended (`tableEntryValue_actual = 1/2` at the two-entry table, mesh `4`).
- Severity: imprecision (mandate).

## F-17 — Talk 2024-10 p. 28: "if these long descriptions `Q` are just conjunctions of claims about real variables, this probably follows from real coherence" (imprecision)

- Pointer: [Understanding Trust talk 2024-10.pdf](../../sources/references/bli/slides/Understanding%20Trust%20talk%202024-10.pdf) p. 28, last line.
- Finding: over `paperDP T` hypothetical marginalization follows from something weaker and more specific than real-value coherence: the process *decides* every literal `⌜F(q)⌝` (T4.2/T4.3), so any valuation coherent relative to the stage after the entry day is exact on it. Real-value coherence (B) is a different constraint (on threshold profiles of one variable, T2) and is not what forces HM. The "probably follows" is true but for the reason "the literal is a theorem of the process", not "real coherence".
- Severity: imprecision.

## F-18 — The mandate's T3.4 "iff" and the per-day UI claim: what SSC can and cannot import (presentation, for dependents)

- Pointer: mandate T3.3 ("Do **not** claim a per-day `P n F.u ≤ P n (F.inst c) + o(1)` unless…"), §5 ("Exact UI at finite days is a theorem *only* relative to coherence w.r.t. the augmented process").
- Finding: what is proved: UI in the limit for every inductor over the augmented process (`ui_limit_of_union`) and over `paperDP T` with no schema (`ui_limit_paperDP`); exact UI at a day relative to stage coherence (`uiAt_of_coherentOn`). What is **not** proved: the per-day `≲ₙ` form (`ui_perDay_open`, OPEN) — dependents must not cite UI at finite days for the LIA itself. Recorded so that `udt-bli-sist` imports the right theorem.
- Severity: presentation.

## F-19 — "All instances believed" makes any schema inert: T3.5's witness can never be T3.3's (structural; found by audit r1, proved in repair round 1)

- Pointer: mandate §0 ("Load-bearing … **T3.3**, **T3.5** … with an N+ witness") and T3.5 ("the fresh-atom witness carrying the N+"); audit r1 fidelity B2 / adversarial issue 1; [STANDARDS](../../STANDARDS.md) §3 (N+ "exercises the content").
- Finding: at the criterion level, a sentence with limiting belief `1` under an inductor is forced by some stage — every world consistent with that stage holds it (`stage_forces_of_limitingBelief_eq_one`, the contrapositive of non-dogmatism) — hence holds in every completed world (`holds_of_limitingBelief_eq_one`). So for **any** family whose instances all have limiting belief `1`, every `u 🡒 inst c` holds in every completed world whatever `u` is, the schema process is inert in the limit, and `UILimit P F` reduces to `P∞(u) ≤ 1` (`uiLimit_of_inst_limit_one`, no schema needed). Consequences: (i) T3.5 ("all instances believed, the universal `< 1`") and T3.3 ("UI in the limit is a constraint the schema forces") **cannot share a non-degenerate witness** — the package's original `ui_strict_fresh` was graded N+ for both and was degenerate for T3.3, exactly as both audits found; the repair splits them (`ui_free_nontrivial`, free instance atoms with `0 < P∞(u) < P∞(inst c) < 1`, for T3.3; `ui_strict_fresh` regraded N− for T3.5). (ii) At the criterion level the content of T3.5 is only "a sentence the process never decides stays `< 1`" — non-dogmatism on `u`; the universal role of `u` is nominal for any propositional witness. What makes the Gödel case (bli-soto-a-082) more than that is semantic: `u` is a genuine universal whose numeral instances are theorems while `u` is not (`ui_strict_paper_open`, OPEN). (iii) Likewise for T3.7 (b): with theorem instances the sibling prime is inert (`⊤` entails the instances), so the sibling mechanism needs undecided instances (`secondLimit_fails_free`) — F-6 (i)/(ii).
- Severity: imprecision (in the mandate's grading plan: it asked for an N+ that cannot exist); no source claim affected. For dependents: any "universal instantiation" theorem cited over a family whose instances are theorems of the base is vacuous at the limit; cite `ui_free_*` or `ui_limit_paperDP` with an independent `φ` instead.
