# Decision problems as instrumental-variable designs: the draw as instrument, forcing as non-compliance, and what fails in Newcomb and Troll Bridge

**AI-derived and unvetted.** Written 2026-09-19 by a Claude Code subagent (Fable 5.1) for the research-direction plan following [smoking-lesion-exploration-and-boundaries](../smoking-lesion-exploration-and-boundaries.md) and [two-lesions-exchange-2026-09-19](../two-lesions-exchange-2026-09-19.md). Direction addressed: *decision problems as instrumental-variable (IV) designs — the draw as instrument, forcing as non-compliance, and what fails in Newcomb and Troll Bridge.* Nothing here has been checked by a person. Grades: **[checked]** = exact enumeration in the scripts of §9 (Fractions, no sampling unless said); **[derived]** = argument from the v2 definitions given here; **[reconstructed]** = a source or a piece of econometrics as I recall it; **[guess]**. Claims about what a person meant are **ATTRIBUTION-UNVETTED** per `epistemic-discipline`. The Two Lesions doc ([two-lesions-doc-2026-09-18](../two-lesions-doc-2026-09-18.md)) became available mid-task and is cited by its section and result numbers; it is itself AI-drafted under the author's direction and unvetted.

**Headline, with register.** The v2 run semantics *is* a randomized-assignment design: Definition 6 is IV independence, Definition 7 recording is perfect compliance plus no selection on the instrument, and the double lesion (doc Definition 2, read as the note's *overwrite* tree) is a two-sided-non-compliance trial in which the agent's draw is a valid instrument, ITT on cancer is exactly 0 and Wald identifies the effect of the act on compliers as α [checked]. Own-policy variation identifies the same structure from two policy values without per-episode tags, on both the bypass and the overwrite tree, because every observable is affine in the label [checked] — Proposition 4 with k = 1. The IV assumptions hold in Newcomb (Definition 6) and the ITT verdict there is two-boxing, which loses: Newcomb is the case where the design is valid and the estimand is the wrong one, exactly the author's correction to the exchange [derived; the correction's reading ATTRIBUTION-UNVETTED]. Troll Bridge is the case where *independence* fails for the proof-respecting agent (doc Lemma 8) and holds, self-fulfillingly, for the agent that stipulates it (doc Proposition 10) [derived]. The two intrinsic counterfactuals of v2 §8 are the two ITTs: on the live draw within O_d (Theorem 1's forcing at the real node, R2-real) and on the any-instance draw within occ(d) (Theorem 2's all-instance deviation) [derived; the mugging instance checked].

---

## 0. Vocabulary, and which reading of the double lesion the mapping needs

IV design [reconstructed, standard]: instrument Z, treatment D, outcome Y, unobserved confounder U of D and Y. Assumptions: **relevance** (Z moves D); **independence / exogeneity** (Z ⊥ U and the potential outcomes); **exclusion** (Y depends on Z only through D); **monotonicity** (no defiers: no unit with D(1) = 0, D(0) = 1). Compliance types: compliers D(z) = z, always-takers D ≡ 1, never-takers D ≡ 0, defiers. **ITT** = E[Y | Z=1] − E[Y | Z=0]; the **Wald** ratio ITT / (E[D|Z=1] − E[D|Z=0]) identifies **LATE**, the effect of D on compliers (Angrist–Imbens–Rubin). Three trial analyses: **as-treated** (condition on D), **per-protocol** (drop non-compliers), **ITT** (condition on Z). Heckman–Vytlacil's **policy-relevant treatment effect** is the effect of shifting the assignment *propensity*, integrated over the units whose treatment flips [reconstructed, moderate confidence on the attribution].

The double lesion (doc Definition 2): states L, A, N with ε_L, ε_A, 1−ε_L−ε_A; cancer iff L; in L the agent smokes w.p. δ "regardless of its policy", in A abstains w.p. δ regardless, else acts on policy p. The note's §1 generalizes cancer to Bern(γ₁)/Bern(γ₀) and splits the "regardless" into two trees with one run law over (ℓ, ℓ′, m, k): **bypass** (forced runs never consult d) and **overwrite** (d consulted, draw replaced). The doc's Definition 2 is neutral between them (its own second remark makes it neutral between per-episode and per-agent readings too). **The IV mapping with the draw as instrument needs the overwrite reading:** an instrument must take a value on every unit, and only the overwrite tree gives every episode a draw Z with forcing appearing as D ≠ Z. On the bypass tree the forced episodes are *unassigned units whose outcomes sit in the same registry* — a sampling contamination, not non-compliance — and the whole IV apparatus (compliance types, Wald) is idle: within the assigned population compliance is perfect. Both readings are handled at once by the draw coordinate of §4, with ⊥ for "not consulted". [derived]

The doc's tag (Definition 3: the record says whether the act was *forced or chosen*) is **not** the draw coordinate on the overwrite tree: it marks the forcing event, which the draw coordinate reveals only when the draw disagrees with the forced act. It *is* the draw coordinate on the bypass tree (chosen ⟺ consulted ⟺ draw ≠ ⊥). The doc's tagged causal learner (Definition 4) is a per-protocol analysis with an oracle for compliance type; the draw-coordinate agent does ITT instead and needs no oracle. §2(B3) prices the difference. [derived; checked]

---

## 1. The mapping (question a)

| v2 notion | IV notion | remarks |
|---|---|---|
| Definition 6: the draw at a decision node is sampled "independently of everything so far" | **independence / exogeneity** of Z from U (and from the observation: randomization within O_d-strata) | stronger than IV independence upstream (independent of *everything*), silent downstream — the continuation may depend on the draw arbitrarily, so exclusion is a separate property of the tree. **Relevance** is Definition 6 plus a mixed label: a deterministic C(d) is an instrument with no variation. |
| Definition 7 recording, clause "exactly one d-node on every O_d-run" and coverage | every O_d-unit is assigned once | coverage failure = unassigned units in the registry (the bypass tree; S2's reference-class home). |
| Definition 7, subtree-veridicality of the node met on O_d-runs | **no selection on the instrument** | Remark 3.4's routing-node selection bias — ν(a \| O) = 1 ≠ ½ — is exactly "the instrument determines inclusion in the analysis sample" (collider bias on O). |
| Definition 7, action-veridicality and "an action in A_d only if drawn there" | **perfect compliance**, D = Z | under recording the IV collapses to a randomized experiment on the act itself; Lemma 3′ (S4) is the resulting "flat pre-query conditionals". |
| post-draw chance and payoff depend on the draw only through m | **exclusion** | holds in the double lesion (k reads ℓ only, r reads m, k). Under Definition 6 a second node carrying d draws *independently*, so a simulation is **not** a draw-level exclusion failure; under Definition 6′ (shared seed, Q12) the live draw is reused there and exclusion fails. |
| forcing to a *fixed* action regardless of the draw | **monotonicity** holds: lesion-forced runs are always-takers, anti-forced runs are never-takers; **no defiers** | the anti-lesion is a never-taker population, not a defier one. A "contrarian" overwrite m := 1 − a would be defiers; with homogeneous effects Wald would still return α (constant-effect 2SLS needs no monotonicity) [derived]. |
| both lesions present | **two-sided non-compliance** | one-sided (lesion only) is S2's one-sided rows: the abstain instrument value is then never overridden. |
| the label C(d)(a) = p | the **assignment propensity**, a design parameter — *not* a random variable of the trial | v2 agrees: Proposition 4, "no label can report q". Its variation across regimes is the "policy as instrument" of §5. |

So Definition 6 answers "which variation is exogenous" by type: the draw. That is the exchange's "the one exogeneity claim it makes is 'my own coin flips are random'" and the note's channel-3 boundary (a draw correlated with an upstream variable is not a Definition-4 procedure under Definition 6). [derived]

---

## 2. Identification (question b) — script `double_lesion_iv.py`, output in §9

Parameters of the note's §1 unless stated: ρ = ρ_A = 1/10, γ₀ = 1/20, γ₁ = 3/5, δ = 1/20 (also asymmetric δ_L = 1/20, δ_A = 1/50), α = 1, β = 10; κ := 1 − ρδ_L − ρ_Aδ_A.

**(B1) [checked] Same run law, affine observables.** The bypass and overwrite trees have identical marginals over (ℓ, m, k) at every p; P_p(m=1), P_p(k∧m=1), P_p(k∧m=0) have exactly zero second differences over p ∈ {0, ¼, ½, ¾, 1}. Explicitly P_p(m=1) = ρδ_L + κp, P_p(k∧m=1) = ρδ_Lγ₁ + κ c_C p, P_p(k∧m=0) = ρ_Aδ_Aγ₀ + κ c_C(1−p), with c_C := [ρ(1−δ_L)γ₁ + (ρ_A(1−δ_A) + 1−ρ−ρ_A)γ₀]/κ the compliers' cancer rate; at γ₁ = 1, γ₀ = 0 these are the doc's §3 explicit forms verbatim.

**(B2) [checked] Two policies identify.** From p = 3/10 and 7/10: forced-smoke mass ρδ_L, forced-abstain mass ρ_Aδ_A, complier mass κ, cancer among forced smokes γ₁ (= 3/5), among forced abstentions γ₀ (= 1/20), among compliers c_C for *either* act (the two slopes sum to exactly 0 — the ITT-null test). Beyond the exchange's list: ρ(1−δ_L) = κ(c_C − γ₀)/(γ₁ − γ₀), hence ρ and δ_L separately when γ₁ ≠ γ₀; ρ_A and δ_A only as a product unless δ_A = δ_L is assumed. At **one** policy the pooled record is three numbers, fitted exactly by "smoking causes cancer" — nothing is identified. So the exchange's identification claim is confirmed, with the two-value requirement being the k = 1 case of Proposition 4 (§5).

**(B3) [checked] ITT and Wald on the overwrite tree at a single interior policy** (p = ½ and p = 1/20 give identical numbers): first stage P(m=1|a=1) − P(m=1|a=0) = κ = 99/100; ITT on cancer = **0** exactly; ITT on payoff = ακ; **Wald = α = 1**, the effect of the act on compliers; the cells P(k | a=1, m=0) = γ₀ and P(k | a=0, m=1) = γ₁ are the never-takers and always-takers read off directly. The **naive matched-episodes estimator** P(k | a=1,m=1) − P(k | a=0,m=0) = 11/3980 ≈ 0.0028 ≠ 0: lesion-forced always-takers who happened to draw smoke are indistinguishable from compliers, so "drop the visible non-compliers" is a biased per-protocol analysis; the doc's Proposition 6 avoids the bias only because its tag marks the forcing event itself. The as-treated gap P(k|m=1) − P(k|m=0) is 0.0055 at p = ½ and 0.0459 at p = 1/20 — the confounded conditional the untagged learner acts on.

**(B4) [checked] Bypass tree.** μ(occ(d)) = κ; within occ(d), a = m on every run, P(k|a=1) − P(k|a=0) = 0, E[r|a=1] − E[r|a=0] = α. The pooled OC-⊤ gap equals the overwrite tree's. ITT on the bypass tree *is* per-run SSC (Claim 1.2 of the note).

**What differs between the trees for identification: nothing at the pooled level, everything at the per-episode level.** [derived] Both trees are identified by two policy values with the same estimates. On the overwrite tree a draw-observing agent identifies everything from **one interior** policy (B3); on the bypass tree an occurrence-observing agent does the same by restriction (B4). A deterministic agent (p ∈ {0,1}) with draw access sees only one instrument value and needs a second policy after all — the exchange's "a deterministic agent has no exogenous variation".

**Does the ITT route need the intention observed?** Overwrite tree: yes for the single-policy route (Z must be recorded), no for the two-policy route, which needs instead *knowledge of the label* (self-transparency of the mixture, Appendix B item 2 — never of the draw, S10/C2-1) and **stationarity across the policies compared**. Bypass tree: the intention exists only on consulted runs, so "observing the draw" means knowing one was consulted (occ(d)); the two-policy route substitutes as before. [derived]

**(draw, act, outcome) vs (act, outcome) with known p — what each identifies that the other cannot.** [derived] Tags at one interior p identify the full forcing structure and are robust to drift in ρ over time (the comparison is within one time slice); label variation without tags needs k+1 policy values for k consultations per path and a stationary environment (the agent's policy trajectory is confounded with time otherwise). Conversely label variation reveals the **degree** of the observables in p — the number of times the label is consulted per path (Proposition 4) — which a tag at fixed p cannot: in Newcomb P_p(fill ∧ one) is quadratic (§9, second differences 1/10) while the within-policy act-conditional of fill is flat; that conjunction is the signature of a hidden consultation, and only the label route sees it.

**(B5) [checked] Heterogeneous effects (Egan's variant: smoking causes cancer iff lesion).** ITT on payoff = 187/400, LATE = 17/36 = α − β·ρ(1−δ)(γ₁−γ₀)/κ, ATE over all runs = 9/20; ITT = κ·LATE exactly. LATE ≠ ATE because the lesion-forced always-takers, who would be hurt by smoking, are not compliers — and they are exactly the runs the agent's draw cannot reach, so LATE is the effect the draw can *realize* (§6).

---

## 3. Which IV assumption fails, and for whom (question c) — `predictor_problems.py`, output in §9

Z is the agent's draw at the real point unless stated; "draw-level" = E[r | Z=a, O] (the ITT within the observation, = R2-real); "policy-level" = V_B(p=1) − V_B(p=0). Numbers: Newcomb sample-skill 9/10, L = 10, S = 1; XOR termites 1/100, cost 100, payment 1; mugging x = 1, y = 3; all at p = ½ [checked].

| problem | Z | assumption status | for whom it fails | draw-level → policy-level | winner |
|---|---|---|---|---|---|
| double lesion, bypass | draw at consulted node; ⊥ on forced runs | all four hold on occ(d); **coverage** fails (unassigned units in the registry) | the OC-⊤ agent pooling unassigned runs (as-treated, confounded); nothing fails for the SSC / draw-conditioning agent | smoke → smoke | both right |
| double lesion, overwrite | draw; D = m | **all four hold**; two-sided non-compliance | the agent without the draw coordinate has *no instrument* (as-treated); the mismatch-per-protocol shortcut is biased O(δ) (B3) | smoke → smoke | both right |
| Newcomb, Omega samples the label (Def 6), perfect or fallible sample-skill | live draw | **all four hold** at the draw level (fill ⊥ draw within p: 1/2 vs 1/2); relevance fails for deterministic C | nobody at the draw level — what fails is *outside IV*: the assignment propensity p is itself a cause of Y (fill is affine in p) | two-box (−1) → one-box (+7) | policy-level |
| Newcomb, exploration bit **unpredictable to Omega** | the bit | all four hold | same as above; the author's correction: the agent "does poorly precisely when the interventionist assumption fits reality well" | two-box → one-box | policy-level |
| Newcomb, Omega reads the bit / seed (Def 6′) | the bit | **exclusion fails** (Z reaches the box: fill 9/10 vs 1/10 within p) | the IV analyst; the EDT-on-draw agent one-boxes and wins | one-box (+7) → one-box (+7) | both right |
| XOR blackmail (Def 6) | draw at the letter point | all four hold (termites 1/100 vs 1/100 within p) | nobody | refuse (−1) → refuse | both right |
| XOR blackmail (Def 6′) | same | **exclusion fails** (termites 1 vs 0 within p) | the EDT-on-draw agent pays (+99) and loses | pay → refuse (−0.99) | policy-level |
| counterfactual mugging (Def 6) | draw at the tails point | all four hold at the real node; the disposition's payoff arrives on H-runs, which have **no live draw** | the draw-level analyst: the y-channel is invisible from the T-registry | refuse (−1) → pay (+1) | policy-level |
| Troll Bridge, proof-respecting 𝔄 | deliberate crossing | **independence fails**: T ⊢ Cross → □⊥ (doc Lemma 8), so Z entails U; relevance fails in consistent worlds (𝔄 never crosses); the predecessors' record is about other units (Cross_M, doc §7 end) | 𝔄, and any agent satisfying the doc's (β) | stay | wrong |
| Troll Bridge, external coin | coin | **binding** coin: valid, coin-crossings are safe and learned safe; **advisory** coin: compliance is U-correlated (fine for LATE) but deliberate crossings stay Löb-bound; **exploring-agent troll** (punishes coin-crossings): exclusion fails, the coin is a direct cause of Blow | the agent whose deliberation can veto the coin; every agent under the stricter troll | cross on the coin | partly |
| Troll Bridge, the note's §9.3 FDT learner / doc's 𝔅 | its own crossing | independence holds **by policy** ("□⊥ an exogenous root, the act an intervention", doc Prop 10) and is self-fulfilling: T ⊬ Cross_𝔅 → □⊥ | nobody; the fragility remark (doc §7) says any agent evidential *about itself* is re-afflicted | cross → cross | right |
| 5-and-10 with a spurious proof | draw | **relevance fails** (deterministic: no variation); the untaken act's conditional is unidentified and a Löbian proof fills the null cell; Definition 10 trembles / ε-chicken restore relevance and, PA being sound, refute the proof | the zero-respecting deterministic agent (Proposition 8's C₀) | take 5 | wrong |

Grades: the four numeric columns [checked]; the assumption diagnoses [derived]; the Troll-Bridge rows lean on the doc's Lemma 8 / Prop 10 as read here [reconstructed].

**Reading the table.** [derived] The draw-level IV verdict is right in the double lesion and XOR under Definition 6, and in Newcomb under 6′; wrong in Newcomb and the mugging under 6 and in XOR under 6′. The policy-level (dose-response in the label) verdict is right in every row where it is defined. Whether the draw is a *valid* instrument (Definition 6 vs 6′) is therefore uncorrelated with whether acting on it *wins* — this is Q6's "no neutral referent" in IV clothing: exclusion at the draw level is a fact about the problem, and its holding is not what makes the draw-level estimand the right one. What is consistently right is the estimand that varies the thing the environment actually reads: the label when the environment samples the label (Newcomb, mugging), the draw when it reads the draw (6′), and either when it reads neither (double lesion). This is the exchange's "condition on the clean source", corrected: not the *clean* source, the *read* source. The author's correction to the exchange — the exploration-as-intervention story explains CDT's failure backwards — is the Newcomb rows: the exploration bit is a valid instrument exactly when Omega cannot read it, and that is exactly when its verdict loses [derived; the correction is quoted, its intended scope ATTRIBUTION-UNVETTED].

**Troll Bridge in IV words.** [derived] For 𝔄 the instrument is endogenous in the strongest possible way — Z ⇒ U is a theorem — so no amount of variation identifies anything: "in a formalism of frequencies there is nothing for a theorem to be but a frequency of 1" (doc §8). The bounded 𝔄_M's safe crossings are an experiment on a *different treatment variable* (Cross_M), for which independence held; carrying its LATE to Cross is an external-validity error, and the doc's §7 last paragraph says exactly this. Note that the exchange's retracted sentence — the agent "trusting experiments its predecessors ran, in a world that responds to something those experiments couldn't vary" — is *wrong of Newcomb* (the author's correction) and *right of Troll Bridge* in the doc's own framing; the direction should not lose that. 𝔅 and the FDT learner make independence true by declining to treat their draw as evidence about U; in the double lesion the same independence is a fact of the tree that the agent could test (B3), in Troll Bridge it is untestable from inside (Gödel) and self-fulfilling (Prop 10). IV validity is agent-relative there — the doc §8's "the confound itself depends on the agent".

---

## 4. Draft for v2 (question d)

**Draw coordinate.** For each queried point d add a coordinate a_d with values A_d ∪ {⊥} to 𝓔, and let the draw-lifted problem B^a carry the same tree, payoffs and λ, with λ^a(ℓ) := (λ(ℓ), (a_d(ℓ))_d) where a_d(ℓ) is the action drawn at the d-node on the root-path of ℓ if that path contains exactly one d-node, else ⊥. This is well-typed: a leaf determines its path, so the draw at each node is a function of the leaf and Definition 5's leaf-world can carry it (a partial version of Proposition 2's lift, adding only the draws rather than the whole leaf identity). Definition 6 is unchanged. [derived]

**Definition 7′ (draw-recorded; act-recorded).** B is *draw-recorded at d* (for C) if μ-a.s. every O_d-run passes at most one d-node and every d-node met on an O_d-run is subtree-veridical; it is *act-recorded* if moreover it records at d in Definition 7's sense (coverage, action-veridicality, act written only by the draw). Act-recorded ⇒ draw-recorded. The overwrite tree is draw-recorded, not act-recorded (action-veridicality fails); the bypass tree is draw-recorded with a_d = ⊥ on the uncovered runs (coverage fails). [derived]

**Proposition D (ITT = forcing; ITT on occurrences = deviation).** Let B be draw-recorded at d for C under Definition 6, a ∈ A_d with C(d)(a) > 0, ν(O_d) > 0, and let N_d^ver be the d-nodes met on O_d-runs. Then
(1) μ(X | a_d = a, λ ⊨ O_d) = Σ_{q ∈ N_d^ver} R_q(C) θ_{q,a}(X) / Σ_{q ∈ N_d^ver} R_q(C) for every X, where θ_{q,a} is the law of the continuation below the a-edge of q; in particular E[r | a_d = a ∧ O_d] = Σ_q R_q G_q(C,a) / Σ_q R_q — the reach-weighted single-instance forcing value at the real nodes (R2-real in the run's vocabulary; Theorem 1's G_q when d has one node).
(2) If moreover every run passes at most one d-node, then μ(X | a_d = a) = μ_{C[d↦a]}(X | occ(d)), so E[r | a_d = a] = E_{μ_{C[d↦a]}}[r | occ(d)], Theorem 2's evaluator, and argmax_a E[r | a_d = a] = argmax_a V_B(C[d↦a]).
No action-veridicality is assumed: (1) is C2's Lemmas L1–L3 (S9) with the *draw event* replacing the *world event* {a ∧ O_d}, which is what lets it hold on the overwrite tree.

*Proof sketch.* Definition 6 factors μ(reach q, draw a at q, X) = R_q · C(d)(a) · θ_{q,a}(X), with R_q free of C(d) when no d-node lies above q (Lemma 1) and θ_{q,a} depending on the path only through q. Under draw-recording, {a_d = a} ∧ {λ ⊨ O_d} = ⋃_{q ∈ N_d^ver} {reach q, draw a} up to μ-null sets: non-veridical d-nodes lie on runs outside O_d, and O_d-runs with no d-node have a_d = ⊥. Summing and dividing cancels the common factor C(d)(a), giving (1). For (2), occ(d) = ⋃_q {reach q} over all d-nodes (Lemma 1's proof), and the deviation C[d↦a] follows the a-edge at each of them, so μ_{C[d↦a]}(X ∧ occ(d)) = Σ_q R_q θ_{q,a}(X) with R_q unchanged; dividing by μ(occ(d)) = Σ_q R_q gives the same expression as μ(X | a_d = a) computed from the factorization. Theorem 2's argmax identity then transfers. □ [derived; the mugging instance of (1) = −x and (2) = ½(y−x) checked, §9]

**Corollary D′ (compliance adjustment).** Suppose in addition that d is *act-symmetric* at each q ∈ N_d^ver: the subtrees below the edges of q are the same chance tree, differing only in which action coordinate value is written, and payoffs and post-draw chance read the draw only through the act coordinate m (exclusion). Couple the post-draw chance across the edges. Then every run has potential acts m(a′) for each a′ ∈ A_d, compliance types are defined, no run is a defier when forcing is to a fixed action, and for binary A_d the Wald ratio [E(r | a_d=1, O_d) − E(r | a_d=0, O_d)] / [P(m=1 | a_d=1, O_d) − P(m=1 | a_d=0, O_d)] equals E[r(m=1) − r(m=0) | complier, O_d] — the standard Angrist–Imbens–Rubin argument, whose hypotheses are now properties of the tree. On the double lesion it returns α (B3). The ITT of Proposition D needs no coupling; the LATE does — a v2 tree has no canonical "same run under a different draw", and act-symmetry supplies one. [derived]

**Remark (self-knowledge).** Strict calibration at a draw-recorded point forces P_{s_d}(a_d = C(d)) = 1 for deterministic C (the recording argument of Remark 3.6 runs on the draw coordinate unchanged), and for mixed C forces only self-transparency of the *mixture* — the state knows the assignment propensity, never the assignment (S10/C2-1). That is the analyst's position in a trial, and it answers the note's §7 question 2 cost: forced knowledge of the draw is forced knowledge of the *act* only under act-recording. [derived]

**What this formalizes from the run.** S2's two homes become two cells of the draw coordinate: {a_d = ⊥} (coverage failure, screened by conditioning on a_d ≠ ⊥, i.e. occ(d)) and {a_d ≠ ⊥, m ≠ a_d} (action-veridicality failure, screened by conditioning on a_d rather than m); S2's "enriching the algebra with a `who` or draw coordinate dissolves both homes" is Proposition D with one coordinate doing both jobs. S4 (Lemma 3′) is Proposition D(1) restricted to pre-query X at act-recorded points. C1 Open 4's trichotomy at an SSC state — world-event {m = a} vs draw-event of the consulted instance vs disposition — becomes four referents with their analyses: the world-event is the as-treated conditional (confounded on the overwrite tree); the *live* draw within O_d is ITT = R2-real, Proposition D(1); the *any-instance* draw within occ(d) is ITT on occurrences = Def 22, Proposition D(2) — the mugging's "−1 vs +1 for pay" in [sl-synthesis](../sl-workflow/notes/final/sl-synthesis.md) §5.3 item 3 is exactly (1) vs (2); the disposition is the label, not an event (Proposition 4), reachable only through D(2)'s deviation or a policy-interpretation event ρ_d(a) (Remark 4.2). The OC/SSC fork of Proposition 3 reappears at the draw level as the R2-real/Def 22 fork: the symmetric difference occ(d) △ {λ ⊨ O_d} is the set of instances on which "my draw" and "the draw at an instance of my point" part company. [derived]

---

## 5. Policy as instrument: Proposition 4, Remark 5.4, channels, and the misspecified learner (question e)

**Bernstein coefficients are forcing conditionals.** [derived] Proposition 4 writes every event probability on a tree querying d once per path as b₀(1−p) + b₁p with b_j = P(X | j draws of a) — and P(X | one a-draw) is exactly the forcing conditional θ_{q,a}(X) reach-averaged, i.e. Proposition D(1)'s right-hand side. So "the label is an instrument" means: *label variation identifies the Bernstein coefficients, and the Bernstein coefficients are the tag-conditioned laws.* Two policy values identify a degree-1 polynomial; k+1 identify degree k; and the identified coefficients b_j are pattern-*averages* c_S over |S| = j, so with hidden consultations the label route identifies less than a full set of per-node tags would (which nobody has for Omega's node) but more than the agent's own tag at fixed p (which cannot see the degree). Remark 5.4's "branching swallows labels" is the learning-side statement: iterated play at varying p is the experiment; the identified b_j are what "sampling estimates dispositions" estimates.

**A lemma the doc also states (§5, before Proposition 5).** [derived; consistent with (B1)] On a once-per-path tree a record pooled over episodes at policies p₁, …, p_t has exactly the joint frequencies of P_{p̄}, p̄ the mean policy — because each cell is affine in p. Hence the cumulative learner's conditionals are the conditionals *at its historical mean policy*, and the two-policy identification of (B2) can be read off two disjoint stretches of one agent's history with different mean policies.

**Which channel structures own-policy variation identifies** (the note's §4 table), with pooled (m, world) statistics and knowledge of p: [derived]

| channel | identifiable from label variation alone? | what is seen |
|---|---|---|
| 1 state (tickle) | yes, and already screened | separate points with separate labels; flat conditionals within each; the population correlation is the label difference (S5's identity) |
| 2a bypass vs 2b overwrite | the forcing structure yes; **the 2a/2b distinction no** — same run law at every p | decision-irrelevant: both give "smoke"; only the draw coordinate separates them (⊥ vs mismatch) |
| 3a draw corruption with an exogenous *intention* (the lesion biases the realized draw given p) | yes — distributionally identical to 2b | the agent learns "when I intend p my smoking rate is ρδ + κp, the excess smokes carry γ₁"; the decision at the intention level is right. **Channel 3a with introspection is indistinguishable from 2b without it** |
| 3b intention corruption (the lesion or the proof sets p itself; Troll Bridge) | **no** — the instrument is endogenous | the exchange's "variation in p is itself lesion-correlated and the VOI computation is run by the corrupted process"; the doc's §6 "the lesion works through the deliberation itself" |
| hidden consultation of the label (Newcomb, mugging) | yes, by the **degree** in p | fill flat in the act within p, moving with p across p; second differences 1/10 (§9) |
| shared seed (Def 6′) | yes, by the within-policy act-conditional being non-flat | fill 9/10 vs 1/10 at every p |

So label variation identifies everything except one decision-irrelevant distinction (2a/2b) and one decision-critical channel (3b), where nothing the agent controls is a clean instrument. The exchange's boundary ("fix the boundary at the deliberative process and ask whether its variation is clean") is the 3a/3b line: the process's *output* may be corrupted and still be a good instrument at the intention level; its *input* p may not.

**The misspecified learner — `misspecified_learner.py`, `misspecified_learner_H.py`, §9.** The exchange: a misspecified VOI agent "treats P(cancer | abstain) as a fixed parameter, chases a moving target and hovers near p̂ like the cumulative learner." Checked in two regimes, with the learner's conditional read at its mean (cumulative) or current (recency) policy:
- **Doc regime** (ε_L = ε_A = 0.2, cancer iff L, C = 100, π = 1, δ = 0.01; (H) holds): the advantage of smoking is negative at both pure labels and crosses zero at p̌ = 0.1670 and **p̂ = 0.9540** [checked; the doc's Proposition 3 numerics report 0.954]. The greedy cumulative learner converges to **p̂ = 0.9540 from every start above p̌** and to 0 below (doc Proposition 5, reproduced); at δ = 0.1 > δ* it converges to 0 from every start. The recency learner with fixed η = 0.2 stays at 1 − η/2 = 0.9, with η ≤ 0.05 collapses to η/2, and with η_t → 0 heads to 0 (doc Proposition 4, both cases; the doc's own first-order formula puts the switch at η ≈ 0.095 here). **"Hovers near p̂" is confirmed for the cumulative learner in the (H) regime** [checked], and for a smooth-response (softmax) learner only at low sharpness — at τ ≥ 10 the one-step softmax map's upper fixed point is unstable by overshoot, an artefact of the discrete map that the 1/t averaging of the cumulative rule removes.
- **Note's §1 regime** (ρ = ρ_A = 0.1, γ₀ = 0.05, γ₁ = 0.6, β = 10, α = 1, δ = 0.05; (H) fails since βρ(γ₁−γ₀) = 0.55 < α): the smoke label *is* a fixed point, the only interior crossing is p* = 0.0201, and every learner from a start above it converges to **p = 1**, not to an interior p̂ [checked]; the stochastic ε-greedy cumulative learner smokes at rate 0.97 = 1 − ε/2 from all eight seeds. There is nothing to hover near.
Diagnosis: the exchange's sentence holds in the doc's regime and is a statement about (H); under (H) the misspecified learner's terminal policy p̂ = 1 − O(δ) is *not* the well-specified learner's p = 1, and the difference is the O(δ) chosen abstentions it must keep making so that its pooled abstention record stays uninformative — the exchange's "chases a moving target" is that maintenance. The well-specified learner (override hypothesis in the class) identifies κ, ρδ, ρ_Aδ, γ₁, γ₀, c_C from two policies and sits at p = 1 — but the finite-sample check (§9, E4) shows the forced-group cancer rates need N ≫ 1/(ρδ) = 200 episodes per policy to stabilize, while κ and the ITT-null are cheap; the decision needs only the latter. [checked]

---

## 6. LATE, ITT, and the act/draw/disposition question (question f)

**Is LATE the quantity the agent should care about?** [derived] For a decision about *what to draw*, the decision-relevant quantity is the effect of the draw, the **ITT** = κ · LATE: the draw matters only on complier episodes and the agent cannot choose to be a complier. Since κ > 0 the two have the same sign and the same argmax for binary acts, so LATE is decision-equivalent for the verdict and wrong for magnitudes (what an option to smoke is worth). LATE is nonetheless the *right effect of the act* to know, because it is exactly the effect on the runs the draw can reach (B5: the always-takers' would-be harm is outside the draw's reach). Heterogeneity across compliance types is decision-irrelevant for the draw and decision-relevant for anyone who could change the *forcing* (a treatment of the lesion), which is not the agent.

**Which of v2's counterfactuals does it match?** [derived; instances checked] Proposition D says: ITT on the live draw within O_d is the reach-weighted **single-instance forcing at the real nodes** (R2-real) — Theorem 1's G_q sum restricted to veridical nodes, equal to Theorem 1's full sum exactly when every d-node is veridical (H*); ITT on the any-instance draw within occ(d) is Theorem 2's **all-instance deviation**. The two coincide when d is consulted once per path and every node is real (the double lesion: both give ακ) and split otherwise (mugging: −x vs ½(y−x); Newcomb: −S vs (2p_acc−1)L − S, i.e. −1 vs +7). Wald rescales either by the complier mass, which is constant in a, so it preserves the argmax of whichever ITT it divides. "Policy as instrument" — the finite difference V_B(1) − V_B(0) — is Def 22's deviation, and equals ∂V/∂p (Theorem 1's derivative) exactly when V_B is affine in the label (once per path, §8 comment (ii)).

**What this says about act/draw/disposition.** [derived] The trichotomy is the trial-analysis trichotomy plus one: **act** = as-treated (condition on m; confounded whenever someone other than the draw writes m); **live draw** = ITT within the observation (R2-real: the effect of *this* assignment, the environment's response to the label held fixed); **any-instance draw** = ITT within occurrences (Def 22: "I might be the simulation", Remark 3.10); **disposition** = the policy-relevant effect of shifting the propensity, never a world-event on the unlifted algebra (Proposition 4), reachable as a parameter by label variation or as an event by identifying one's draw with every instance's draw. v2's own verdict (Theorem 2, Remark 8.1: the coherent-care functional is the one whose ratifiable points contain the optimum) selects the third/fourth, and the table of §3 agrees: the disposition-level estimand is the one that is right in every row. The IV vocabulary does not adjudicate CDT vs EDT — it relocates the dispute to "which variable does the environment read", which is Q6's absence-of-a-neutral-referent stated as a fact about designs rather than about counterfactuals.

---

## 7. What to say, with registers

1. **Definition 6 is IV independence; Definition 7 recording is perfect compliance plus no selection on the instrument; the double lesion on the overwrite reading is a two-sided-non-compliance trial with the anti-lesion as never-takers, no defiers.** [derived]
2. **On the overwrite tree, ITT on cancer is exactly 0 and Wald identifies α from one interior policy; the doc's tag is finer than the draw coordinate (it marks the forcing event) and the mismatch-based per-protocol shortcut is biased by 11/3980 at the note's parameters.** [checked]
3. **Two policy values identify the forcing rates, both forced-group cancer rates and the compliers' rate on both trees identically; one policy identifies nothing; the requirement is Proposition 4 at k = 1.** [checked]
4. **Newcomb under Definition 6 is a valid IV design whose ITT verdict (two-box) loses; the exploration bit is a clean instrument exactly when Omega cannot read it — the author's correction, made exact.** [checked for the numbers; the reading of the correction ATTRIBUTION-UNVETTED]
5. **Troll Bridge: independence fails for the proof-respecting agent as a theorem, holds by self-fulfilling stipulation for 𝔅 / the FDT learner; the exploring-agent troll is an exclusion failure for the coin; the predecessors' record is an external-validity failure.** [derived from doc Lemma 8 / Prop 10 as read here]
6. **Proposition D: at draw-recorded points, ITT on the live draw within O_d equals single-instance forcing at the real nodes (R2-real) with no action-veridicality needed; ITT on the any-instance draw within occ(d) equals Theorem 2's deviation; C1 Open 4's two SSC verdicts on the mugging are these two.** [derived; instances checked]
7. **"Hovers near p̂" holds for the cumulative misspecified learner under the doc's hypothesis (H) (p̂ = 0.9540 reproduced) and fails in the note's §1 regime, where the smoke label is itself the attractor.** [checked]
8. **Own-policy variation identifies every channel structure of the note's §4 except the decision-irrelevant bypass/overwrite distinction and channel 3b (intention corruption), where no agent-controlled instrument is clean.** [derived]

---

## 8. Questions for the author

1. The IV mapping needs the overwrite reading of the doc's Definition 2; the doc's Definition 3 tag is then a forcing-event oracle rather than a draw record. Do you want the doc's "chosen" to mean "the act followed my draw" (observable, biased per-protocol) or "no forcing occurred" (Proposition 6's reading, unobservable without an oracle)? The verdicts agree; the estimators do not.
2. Should the draw coordinate of §4 be the default in v3, with Definition 7′'s draw-/act-recorded split and Proposition D as the formal home of "recording the draw dissolves the compulsion" (L1.md:17)?
3. Proposition D(2) reads Omega's simulation draw as "my draw" when the simulation is the only d-node on its path. Is that the anthropic identification you want made explicit (Remark 3.10), or should the coordinate record only live draws and leave Theorem 2's referent to the label?
4. The exchange's retracted "predecessors' experiments" sentence is right of Troll Bridge (doc §7 end) and wrong of Newcomb. Worth keeping under its correct problem?
5. §3's reading: the draw-level design is valid or invalid independently of whether its verdict wins, and the label-level dose-response wins in every row. Is "condition on the variable the environment reads" an acceptable non-question-begging replacement for "condition on the clean source", or does it beg the question one level up (the environment's reading is itself construal-dependent — Def 6 vs 6′, S11)?

---

## 9. Numerical appendix (excerpts; full outputs in the `.out` files beside the scripts)

`double_lesion_iv.py`, symmetric δ = 1/20:
```
(B1) observables (P(m=1), P(k&m=1), P(k&m=0)) at p=0,1/4,..,1 [identical on both trees]:
   p=0 (1/200, 3/1000, 51/500)   p=1/2 (1/2, 431/8000, 409/8000)   p=1 (199/200, 419/4000, 1/4000)
   second differences all exactly 0: each observable is affine in p
(B2) identification from p=3/10 and p=7/10:
   rho*dL = 1/200 (true)  rhoA*dA = 1/200 (true)  kappa = 99/100 (true)  gamma1 = 3/5 (true)  gamma0 = 1/20 (true)
   cancer | complier, either act = 37/360 ; slopes sum to 0 (ITT-null test)
   rho(1-dL) = 19/200 -> rho = 1/10, dL = 1/20 ; rhoA, dA only as a product unless dA=dL
(B3) OVERWRITE p=1/2: P(m=1|a=1)=199/200 P(m=1|a=0)=1/200 -> first stage 99/100
   ITT on cancer = 0 ; ITT on payoff = 99/100 ; Wald/LATE = 1 = alpha
   naive P(k|a=1,m=1)-P(k|a=0,m=0) = 11/3980 ; P(k|a=1,m=0) = 1/20 ; P(k|a=0,m=1) = 3/5
   as-treated gap P(k|m=1)-P(k|m=0) = 11/2000 (p=1/2), 0.0459 (p=1/20)
(B4) BYPASS p=1/2: mu(occ(d)) = 99/100 ; within occ(d) ITT on cancer 0, on payoff 1 ; a==m on occ(d)
(B5) Egan variant: ITT = 187/400 ; LATE = 17/36 ; ATE = 9/20 ; ITT = kappa*LATE
```
`predictor_problems.py`, p = ½:
```
Definition 6:  Newcomb  draw-level -1 (two-box)  policy-level +7 (one-box)  fill|two=1/2 fill|one=1/2  P_p(fill&one) degree 2
               XOR      draw-level -1 (refuse)   policy-level -99/100      termites|refuse=1/100 = termites|pay
               mugging  draw-level -1 (refuse)   policy-level +1 (pay)
Definition 6': Newcomb  draw-level +7 (one-box)  policy-level +7            fill|two=1/10 fill|one=9/10 (exclusion fails)  degree 1
               XOR      draw-level +99 (pay)     policy-level -99/100      termites|refuse=1 termites|pay=0 (exclusion fails)
               mugging  draw-level within O_T -1 ; within occ(d) +1 (= all-instance deviation) ; policy-level +1
```
`misspecified_learner_H.py`:
```
DOC REGIME (eps=0.2, C=100, pi=1, delta=0.01; (H) holds): crossings 0.1670, 0.9540 ; abstain fixed, smoke not
   cumulative greedy: start 0.001/0.05 -> 0.0000 ; start 0.2/0.5/0.9 -> 0.9540
   recency: eta=0.2 -> 0.9 (from 0.5, 0.95), 0.1 (from 0.05) ; eta=0.05 -> 0.025 ; eta_t -> 0 -> 0.0071 heading to 0
   delta=0.1 > delta*: no interior crossing; every learner -> 0
NOTE REGIME (rho=0.1, g=(0.05,0.6), beta=10, delta=0.05; (H) fails): crossing 0.0201 ; both pure labels fixed
   cumulative greedy: start 0.001 -> 0 ; start 0.05/0.2/0.5/0.9 -> 1.0000 ; recency eta_t->0 -> 0.9929
```
`misspecified_learner.py` (note regime): ε-greedy stochastic cumulative learner, 8 seeds, smoking rate 0.967–0.975 over the last 5000 of 20000 episodes; well-specified two-policy estimator at N = 2000 / 20000 / 200000 per policy: κ = 1.010 / 0.978 / 0.991 (true 0.990), γ₁ = 8.3 / 0.41 / 0.45 (true 0.60) — the forced-group rates divide by ρδ = 0.005 and are slow; κ and the ITT-null are fast.

---

## File map

Wikilink → repo path (repo root = inner-sandbox):

| Link | Path |
|---|---|
| [smoking-lesion-exploration-and-boundaries](../smoking-lesion-exploration-and-boundaries.md) | `research/decision-problems/smoking-lesion-exploration-and-boundaries.md` (§1 the two trees; §2 agent vs environment noise; §4 the three channels; §7 question 2; §9.3 the FDT learner) |
| [two-lesions-exchange-2026-09-19](../two-lesions-exchange-2026-09-19.md) | `research/decision-problems/two-lesions-exchange-2026-09-19.md` ("ε dilutes; VOI identifies"; the intention-to-treat rendering; the author's correction on Newcomb) |
| [two-lesions-doc-2026-09-18](../two-lesions-doc-2026-09-18.md) | `research/decision-problems/two-lesions-doc-2026-09-18.md` (Definition 2 the double lesion; Definition 3 tags; Definition 4 causal learner; Propositions 3–7; Lemma 8; Proposition 10; §5 recency vs cumulative learners) |
| `smoking-lesion-thread` | `research/decision-problems/smoking-lesion-thread.md` |
| `decision-problems-v2` | `research/decision-problems/decision-problems-v2.md` (Definitions 5–7, 10, 13, 17, 22; Lemmas 1, 3; Propositions 2–4, 11–12; Remarks 3.4, 3.6, 3.10, 3.11, 4.2, 5.4, 8.1; Theorems 1–2; Q6, Q11, Q12; Appendix B) |
| [sl-defensible-claims](../sl-workflow/notes/final/sl-defensible-claims.md), [sl-synthesis](../sl-workflow/notes/final/sl-synthesis.md) | `research/decision-problems/sl-workflow/notes/final/sl-defensible-claims.md` (S1, S2, S4, S9, S10, S11), `…/sl-synthesis.md` (§1.3 Lemma 3′; §5.3 item 3, C1 Open 4) |
| run ledgers cited by path | `research/decision-problems/sl-workflow/notes/repair/{C1,C2,L1}.md` |
| `epistemic-discipline` | `research/wiki/epistemic-discipline.md` |
| scripts (scratchpad, not in the repo) | [scrubbed] with `.out` files; exact Fractions except the learner simulations. Copy into `research/decision-problems/` if the note is kept. |
