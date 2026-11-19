1. **1E — “proved” is earned only for a narrower theorem with additional assumptions.** The proof in [THEOREMS.md:29](/tmp/legit-review-2026-11-11/teleology/THEOREMS.md:29) is a correct value-of-information argument when the posterior uses one fixed joint model and the later action maximizes the **same utility** used to evaluate the initial action. The bound `gain_k ≥ −D(1−α)/α` is also correct.

   But “let M1 hold, so that … her values are `v_0` and she chooses by them” does not follow. M1 permits endogenous value changes and authorized writes; it supplies neither fixed values nor maximizing choice. `s1_expectations` supplies maximizing choice directly through `best` and never checks M1 or a state trajectory. Retain the proof, but state fixed utility, unchanged available actions, coherent Bayesian conditioning, and maximizing choice as additional hypotheses. The account’s three clauses have not established them.

2. **1V — the refutation is earned; its proposed repair changes the criterion.** `x_value_drift` and `s1_values` correctly exhibit a legitimate V− change whose later choice is worse according to the initial value vector. This is a valid counterexample.

   However, [THEOREMS.md:77](/tmp/legit-review-2026-11-11/teleology/THEOREMS.md:77) then evaluates choices by expected **later** values. The martingale inequality is correct for that criterion; it does not repair the original initial-values inequality. The code itself finds four martingale cases that violate the latter. Accordingly, the report’s “holds under V+” needs this qualification. Also, a martingale requires conditional expectations under a coherent common probability model; independently recomputing `Bayes(R_t)` after arbitrary changes to `R_t` does not automatically establish it.

3. **2 — the negative conclusion is sound, but the named counterexample misses a hypothesis, and the positive repair is false as stated.** The statement quantifies over every aim, while X3 has aims `{NULL, A, B}` and is **not legitimate at NULL**. `s2` checks legitimacy only at A and B ([theorems.py:144](/tmp/legit-review-2026-11-11/teleology/theorems.py:144)). Thus X3 is not the advertised counterexample.

   This is repairable without changing the conclusion: give truthful, advocate-A, and advocate-B sources weight `1/3` each. I checked this construction: all three aims are legitimate, while at world `(1,1)` the credence in B is `1/2` under A and `1` under B.

   More seriously, “uniformly in range and M1 imply equal evaluation” ignores authorized writes. Taking B1 and setting `auth=("b",)` yields uniform inputs and all three clauses at both aims, yet mean evaluation changes from `1/2` at NULL to `1` at B. This follows both from the definitions and from execution. The repair needs identical authorized events across compared aims, or a restriction making every relevant state transition depend on the same protected inputs.

4. **3 — “refuted” is earned for the stated benchmark, but the uniform-source conclusion is only a fixture result.** The gains of `1/8` for advocacy and `1/6` for the known persuasion signal reproduce. A thresholded verdict can change despite an unbiased mean credence.

   The comparison in [theorems.py:233](/tmp/legit-review-2026-11-11/teleology/theorems.py:233) nevertheless ranges over cases with different allowed sets and sometimes different mechanisms. It is not uniformly a comparison of interventions on one fixed principal. The advocacy example can survive that stronger requirement, but the fixture should distinguish it from comparisons that change the principal.

   “No gain under uniform” holds for the eight presentations enumerated, not for the account: the authorized-write example in point 3 defeats the generalization. Likewise, “sound not needed” in the table is a statement about that fixture; a general invariance proof requires all relevant events and transition rules to be fixed. Dropping maintained tests M1 writes, not the necessity of M2.

5. **4 — “proved” is not earned for the gated score; that claim is false.** The elementary bound on a bounded deterministic evaluation is correct when the evaluations agree outside the defect event. But [THEOREMS.md:192](/tmp/legit-review-2026-11-11/teleology/THEOREMS.md:192) extends it to gated `V` without proving that the **gate** agrees there. `s4` checks only raw `evaluation`, never `gate_score`, `Legit`, or `V−λN`.

   Here is a counterexample I executed. Give Shop world `(0,0)` probability `1/1000` and each other world probability `333/1000`. Her sole hypothesis is truthful reporting. NULL reports truthfully; aim B reports truthfully except that it reports B sound in `(0,0)`. There are no writes, and the mechanism is Bayesian.

   The defect event has probability `τ=1/1000`. Nevertheless, the actual source is outside her allowed set **as a function**, so the gate fails across the case. With `δ=1` and window `−1/2`, the null score is `333/500`, the actual score is `−1/2`, and the loss is `583/500`. The claimed bound is only `2τ=1/500`.

   The proof therefore does not establish the requested shortfall result. Nor are measured defects for all three clauses supplied: source disagreement replaces the account’s `1−α`, and capacity loss is not handled. The threshold example correctly shows failure of proportionality to numerical write size, but supplies neither a bound on the full score nor an unbounded-loss example.

6. **5 — the impossibility proof is correct; the sufficiency statement omits M2.** No single source can equal two distinct singleton hypotheses. That part of [THEOREMS.md:217](/tmp/legit-review-2026-11-11/teleology/THEOREMS.md:217) is proved.

   “Declare a representable source, realize it at every aim, write nothing” does not suffice for legitimacy. P10 already has a known, uniform truthful source and no writes, yet fails M2 through reliance. The proof establishes in range and M1, assumes sound, and never establishes M2. Restrict the principal class to sound principals whose capacity remains maintained, and specify how disclosure changes their allowed sets. `s5` tests a class with no reliance events, which conceals this omission.

7. **6 — the restricted computational results hold; the dispatch’s disclosure claim remains unestablished.** The input marginals and mean values in `x_frame_reader` reproduce, as do the 32 exact-source Bayesian calibration checks.

   But equal **unconditional input marginals** do not establish undetectability. In [cases.py:378](/tmp/legit-review-2026-11-11/teleology/cases.py:378), whether the message matches her frame has probability `1` under X, `0` under Y, and `1/2` under NULL. If her frame is accessible to her, the joint observation distinguishes the policies. No observation model or detection criterion is supplied.

   Part (b)’s calibration proof is valid for the Bayesian output itself. It additionally requires the evaluated credence to remain that output: the authorized belief write from point 3 defeats calibration while sound and exact in-range still hold. Neither calibration nor the finite checks establish that a disclosed adviser cannot steer values or verdicts.

8. **7 — the sensitivity counts are correct, but “well-definedness refuted” is largely an artifact of the transformations.** `widened` changes her hypothesized sources, their weights, and sometimes her mechanism. These are substantive parameters of the account, not merely alternative descriptions of the same principal. Their changing verdicts do not establish failure of invariance under a genuine re-description.

   `writes_as_inputs` is also not behavior-preserving: [model.py:203](/tmp/legit-review-2026-11-11/teleology/model.py:203) discards the written value and does not provide a mechanism that executes the newly encoded write. In X6, it removes the mechanism replacement responsible for unsoundness. This is not a demonstrated change of boundary around the same process.

   The original third question concerned the declared-input view; the replacement tests broadening the hypothesis set. The analogy to an injective view is useful, but it is not an instance of `realizes_of_injOn`. The 22/37 legitimacy split and nineteen removed in-range failures are genuine sensitivity results. The requested invariance claim should remain open until “re-description” is defined by a behavior-preserving correspondence. Also, line 284 says manipulation survives neither transformation, contradicting the reported zero manipulation changes for `writes_as_inputs`.

9. **8 — the scoring construction and finite arithmetic are correct; “Theorems 1–3 apply” requires additional structures and hypotheses.** The window construction satisfies `Scoring` for any predicate and natural-valued `N`. The 108-history checks reproduce.

   However, [theorems.py:394](/tmp/legit-review-2026-11-11/teleology/theorems.py:394) checks Theorem 1 and one inequality from Theorem 2. It constructs no sequential system and checks none of Theorem 3’s hypotheses. `Scoring` alone does not instantiate `Decision` or `Sequential`.

   Uniform legitimacy also depends on an entire counterfactual policy family, not just the realized history. To define `Legit : H → Prop`, that family must be fixed externally or included in `H`; the same observed trajectory can otherwise receive different verdicts. Finally, point 3 invalidates the claimed general incentive justification for choosing uniform legitimacy, although it does not invalidate the generic scoring construction.

10. **There is a verdict-changing implementation error: world-dependent writes are evaluated using the first world only.** [model.py:82](/tmp/legit-review-2026-11-11/teleology/model.py:82) sets `w0 = case.worlds[0]` and reads every replacement of `R` or `rho` from that world. Both `sound_at` and `weight` consequently use the wrong state when writes depend on the world.

    I constructed a truthful Shop case with an authorized `rho=misreads` write only in `(1,1)`. In the ordinary world ordering, the code calls it legitimate. Reversing the enumeration of exactly the same worlds makes it fail sound. A verdict must not depend on enumeration order. The supplied bank does not expose this because its relevant mechanism writes are world-independent.

11. **The implementation is an event classifier, not the state-transition model described in the account.** `Case` has no evolving belief/value state, value mechanism, or numeric capacity. Value transitions for 1V and 6 are calculated separately. M1 is essentially an unauthorized-write scan, rather than verification that state changes follow the declared mechanism.

    This matters in [theorems.py:107](/tmp/legit-review-2026-11-11/teleology/theorems.py:107): `evaluation` recomputes a posterior from the complete input sequence and then applies every belief write, regardless of when it occurred. A belief write before later Bayesian inputs therefore overrides those inputs. The bank’s terminal belief-write examples avoid this error.

    `capacity_lost` also treats any reserved reliance as a strict loss, although the account permits initial capacity zero, for which halving loses nothing. These limitations should be explicit domain restrictions or corrected implementations.

    Finally, `K` is described as a set of `(state, source, step)` triples but depends on whether the preceding stretch was maintained. The listed state coordinates do not retain that history. A trace or maintenance certificate is needed to make this a predicate on its stated carrier.

12. **Several case verdicts are selected by the encoding, and some earlier scenarios lose their distinguishing behavior.** The report correctly acknowledges fit, but concrete examples matter:

    - P1/P2 have the same aimed policy; changing the supplied allowed set from neutral to planner determines the different legitimacy verdicts. P3/X2 use the same `beyond` construction with different pictures, which determines whether the null comparison calls the failure manipulation.
    - Teacher, friend, and P14 use a singleton aim set and matching source hypothesis. Their “not manipulation” and uniformity properties are largely fixed by construction.
    - P10/P11 differ by the externally supplied reserved set; their divergence follows from the stipulated reliance rule.
    - P9/N5 authorize an entire coordinate. This omits N5’s original instruction governing **when and what** to write, rather than granting unrestricted access to that coordinate.
    - Original N9 and T7 require order to move her judgment. Their current `order_by_aim` encoding uses a Bayesian mechanism whose final posterior is unchanged by order.
    - Original B4 requires the extra reason to move the endpoint. Current B4 adds `A∧B` after fully revealing A and B, so it adds no Bayesian information.
    - N3 is exactly the same `lie` construction as N1; the payoff change making it beneficial is absent.

    These are changes to the tested scenarios, not merely changes in vocabulary. See [cases.py:319](/tmp/legit-review-2026-11-11/teleology/cases.py:319) and the corresponding earlier-bank descriptions.

13. **The advertised runner does not run unmodified in this supplied directory.** [run.py:19](/tmp/legit-review-2026-11-11/run.py:19) expects `CASE_BANK.md` and `steering/CASE_BANK.md`; the supplied files are under `banks/`. `python3 run.py` terminates with `FileNotFoundError`.

    With only an in-memory adjustment to those two paths, all checks pass and the reported counts reproduce. I changed no files and disabled bytecode generation. This establishes reproducibility of the calculations after the packaging adjustment, not correctness of their interpretations. The runner compares status labels against strings returned by checks; it cannot validate the prose proofs or detect the missing hypotheses above.

14. **The displayed Lean quotations are accurate.** I checked the quoted `Frame`, `LicensedAt`, `Realizes`, `Policy.present`, `tower_factor`, `evalAt`, `OpenAt`, abbreviated `Counted`, `defect`, `GradeTrust`, and `Scoring` declarations against the supplied copies. The cited declaration locations are correct. The important defects are in the asserted correspondences.

15. **`LicensedAt` is not the account’s soundness, and `ReasonMediated` is not M1.** [LEAN_MAP.md:32](/tmp/legit-review-2026-11-11/teleology/LEAN_MAP.md:32) overlooks the existential selector in `LicensedAt`. A singleton Bayesian license requires the verdict to equal Bayes on **selected grounds**, not on the complete input prefix. Selecting no grounds can license the prior despite informative available inputs. `LicensedWhole` at `GateIsLegitimacy.lean:253` is the closer declaration, subject to the other domain differences already noted.

    `ReasonMediated` constrains comparative outputs, not their causal provenance. An unauthorized write producing the same output in every audited continuation can satisfy it. Conversely, an authorized aim-dependent write satisfies M1 but can violate reason mediation. The claimed equivalence at map lines 105–106 is therefore false in both directions.

    `tower_factor` accurately supplies equality when both grounds **and authorized events** agree. Its second requirement is exactly what the uniform-source repair drops. `evalAt` carries a license parameter but does not validate it; its transition equation alone is not a certificate of legitimate authorization.

16. **Several further Lean-map differences need qualification.** In [LEAN_MAP.md:175](/tmp/legit-review-2026-11-11/teleology/LEAN_MAP.md:175), the proposed explicit state reading is useful, but a fixed `Lic` does not make changing standards inexpressible: a fixed function of the grounds can reconstruct a changing standard from an amendment history. What is missing is a supplied encoding and proof, not necessarily a more expressive type.

    Similarly, `Realizes` with one reference gives uniformity only when declared inputs are held fixed across compared aims. It does not prohibit dependence through declared inputs. The map sometimes preserves this qualification; the report’s identification of class-level transparency with uniformity often drops it.

    The claims about `Rows.r19`, `Rows.r20`, the absence of weighted reference families, and the distinction between `OpenAt` and numeric capacity are correct. But “the account’s in range fails a believed lie” is not generally true under `α>0`: a mixture containing truthful and lying sources can remain in range while assigning high credence to the lie.

    Finally, `defect` is a pointwise disagreement indicator, not itself a probability; its expectation is the probability. The stated distinction from hypothesis weight is otherwise correct.

17. **The report needs substantive correction, while several limitations are already candidly reported.** [REPORT-section.md:14](/tmp/legit-review-2026-11-11/REPORT-section.md:14) overstates the expectations result, the uniform-source repair, and the well-definedness refutation. G2/G5 overstate the V+ repair, shortfall theorem, adviser sufficiency condition, and automatic applicability of Theorems 1–3.

    G5’s “no behaviour is legitimate for two principals with different allowed sets” additionally drops the essential **distinct singleton** restriction: different overlapping allowed sets can share a legitimate source.

    G8 correctly acknowledges fitted cases, stipulated capacity, missing detection, and limited enumeration. It nevertheless fails to identify the authorized-write counterexample, the global-gate discontinuity, the first-world implementation error, and the loss of behavior in re-rendered cases. “No statement … uses M2” should be presented as a missing obligation in statement 5, rather than merely a limitation. The report should distinguish reproduced computations, valid restricted proofs, false generalizations, and open semantic bridges.

18. **For corrigibility, this supplies a candidate scoring predicate, not the substantive connection between legitimacy and protected authority.** The precise remaining obligations are:

    - **A meaningful violation count.** `DeconfusingCorrigibility.Scoring` accepts arbitrary `N`. The work must connect it to reserved matters being settled without an authentic, applicable, legitimate judgment from their holder. Assigning `N=1` to one synthetic bypass and zero elsewhere does not establish that connection.
    - **An authority-respecting alternative.** `Decision.theorem2b` requires `Respects astar`, meaning zero violations in every state. The sequential structure separately assumes availability and bounds for the alternative’s estimated score. The account supplies neither a general construction nor preservation of that alternative.
    - **The sequential hypotheses.** [DeconfusingCorrigibility.lean:404](/tmp/legit-review-2026-11-11/lean/DeconfusingCorrigibility.lean:404) requires availability, estimates, chosen actions, and alternative-score bounds; Theorem 3 additionally requires `Maximizes` and `UnbiasedFromFeedback`. Legitimacy does not supply these. A credible feedback argument must address counterfactual policy facts and evolving mechanisms; exact classification of every history is one possible route, not a formal necessity of the aggregate unbiasedness assumption.
    - **A justified evaluation standard.** The account has not established that later value judgments are preferable by initial standards, or that maintained capacity implies improved judgment. It also needs an account of legitimate changes to authorization, mechanisms, and representational capacity that closes the authorized-write gap.
    - **A connection to actual corrective power.** A stipulated unaided-capacity number is not a proof that correction, refusal, revocation, or an adequate fallback remains available. The threat case illustrates the missing treatment of options and consequences.

    The Lean theorems themselves require no richer legitimacy predicate than their explicit assumptions demand. Consequently, wrapping any predicate in the prescribed score window proves the same arithmetic. The research task still outstanding is to justify that this particular predicate and violation count track the authority and judgments corrigibility is supposed to preserve.