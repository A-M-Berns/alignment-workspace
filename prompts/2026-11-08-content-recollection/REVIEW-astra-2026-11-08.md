Reviewed head `5a421912`, including all six changed Lean files. No Lean build or test suite was run.

1. **Conservativity: the requested result is present.**

   The definitions in [Conservativity.lean:107](/Users/anson/hub/repos/alignment-workspace/.claude/worktrees/round-2026-11-08-content-recollection/lean/Workspace/Normativity/Contrib/Conservativity.lean:107) quantify over row consequences independently of region inclusion:

   ```lean
   Refines ... := ∀ r, Forces R r → Forces R' (pull T r)
   AddsNothing ... := ∀ r, Forces R' (pull T r) → Forces R r
   Conservative ... := Refines T R R' ∧ AddsNothing T R R'
   ```

   Thus the statements at lines 128, 206 and 218 have content:

   ```lean
   Refines T B.Region R' ↔ ∀ x, image T R' x → B.Region x
   AddsNothing T R B'.Region ↔ ∀ x, R x → image T B'.Region x
   Conservative T B.Region B'.Region ↔
     ∀ x, image T B'.Region x ↔ B.Region x
   ```

   Only the forward direction of `addsNothing_iff` needs separation. `liftRows` includes the new bundle, cube constraints, and both inequalities expressing `T.apply y = x`; the Farkas coefficients yield an old row satisfied throughout the image and violated at `x`. The signs in `separating_row` are correct.

   The embedding case is recovered by specializing the more general coordinate map. `extend_refines` assumes the same docket, mapped warrants and `SettlementExtends`; `extend_conservative_iff` explicitly states projection equality and its equivalence to lifting every old forced point (lines 284–318). “An extension always refines” needs those qualifications.

   The bad-concept fixture meets the dispatch. At lines 398–428, `badCert` weights the premise, introduction and elimination rows by `3/5, 3/4, 1`; their sum is `−Y ≤ −3/10`. The proof checks satisfaction of those actual extension rows. Its conclusions include:

   ```lean
   LowerBound ext₂ [] DocketState.quiet (Settlement.empty 3) 1 (3/10)
   forcedRegion ext₂ [] DocketState.quiet (Settlement.empty 3)
     ![1/2, 3/10, 2/5]
   ¬ LowerBound seed₂ [] DocketState.quiet (Settlement.empty 2) 1 (3/10)
   ```

   The ruling on strict seed independence is correct: lines 510–522 prove preservation of coordinate equalities under the stated nonemptiness hypothesis, while exhibiting a strict layer that adds an inequality. It is not full row conservativity.

2. **Incompatibility semantics: the mathematical claims hold at the stated scope.**

   [IncompatibilitySemantics.lean:67](/Users/anson/hub/repos/alignment-workspace/.claude/worktrees/round-2026-11-08-content-recollection/lean/Workspace/Normativity/Contrib/IncompatibilitySemantics.lean:67) defines:

   ```lean
   Incompatible L := ∃ m, ∃ c : FarkasCert d m, ∀ i, Allowed L (c.row i)
   ```

   The bridge at lines 71–75 states exactly:

   ```lean
   Incompatible (B.map CitedRow.row) ↔
     ∃ m, ∃ cert : FarkasCert d m,
       (CompileResult.conflict m cert : CompileResult Q d).Valid B
   ```

   This matches `Bundle.Allowed` and `CompileResult.Valid`; it establishes existence of a valid compiler result, not execution of a compiler algorithm.

   The headline is:

   ```lean
   theorem incEntails_iff_certEntails (Γ : List (Row d)) (g : Row d) :
       IncEntails Γ g ↔ CertEntails Γ g
   ```

   No nonemptiness assumption is needed **relative to the cube**. Lines 168–212 combine a cube certificate having the desired coefficient vector with a scaled negative-constant conflict certificate. This correctly covers inconsistent premises.

   In `RowAlternative.lean:90–178`, negating both coefficients and constants converts `a·x ≤ b` into the dependency’s `Ax ≥ b`; negating the objective likewise gives the required certificate inequality. The dependency sources resolve, and their statements match these uses. This introduces a proof dependency already pinned in the manifest, not a new axiom or changed trust-chain pin. The report identifies that accurately.

   Item 118’s deliverable matches the two statements at lines 287–290 and 343–346:

   ```lean
   (h : LowerBound S W st F φ c) :
     ∃ m, ∃ cert : BoundCert d m φ (-1),
       (∀ i, (forcedBundle S W st F).Allowed (cert.row i)) ∧ c ≤ -cert.value

   (hne : ∃ x, forcedRegionR S W st F x) :
     IsForcedInterval S W st F φ
       (forcedInterval S W st F φ).1 (forcedInterval S W st F φ).2
   ```

   The named witnesses instantiate the hypotheses using `widenSeed`, its valid `1/2` bound and an actual feasible point.

   The degeneracy claim is correctly restricted in the report:

   ```lean
   theorem humble_forms_feasible (X : List (Form d))
       (h : ∀ f ∈ X, f.c ≤ 1) : Feasible (X.map Form.row)
   ```

   It does not cover arbitrary strengths, structural constraints or settlement contexts. The PR description’s unqualified “all-ones point satisfies them all” should retain the strength restriction.

3. **`Expresses`: substantive expression discrimination, with deliberately weak surrounding protocol data.**

   [ExpressesByRole.lean:178](/Users/anson/hub/repos/alignment-workspace/.claude/worktrees/round-2026-11-08-content-recollection/lean/Workspace/Normativity/Contrib/ExpressesByRole.lean:178) is genuinely an incompatibility-role definition:

   ```lean
   DemandsNoMore ... := ∀ F X,
     Incompatible (ρ F ++ X) → ReqIncompatible w ι F X

   theorem demandsNoMore_iff ... :
     DemandsNoMore ι w ρ ↔ ∀ μ, w.Models μ → Holds μ ι ρ
   ```

   Both directions work: point-fixing row contexts detect a violating posterior; conflict soundness proves the converse.

   The denotation is exactly nonnegative measures satisfying `Robust` (lines 167–168). Interpretation, events, strengths and undefeated extensions are inputs. Choosing `U := keptExtensions` builds the desired compatibility condition into the requirement; it does **not** independently validate the rebuttal rule’s defeat semantics. Nevertheless, the fixture is not hollow: `μ_models_kept` supplies an actual model, and the same requirement rejects the plain row.

   `entitlementW` is an inhabitant of the repository’s actual `Entitlement`. But the surrounding conditions are easy by construction: every obligation is exposed, `J₀` matches each issuer, every initial account is live, and `protocolW` uses `Unit` resolutions and `True` authentication/liveness predicates (lines 423–470). The expression condition carries the discrimination; this is not a demonstration that all four conditions independently discriminate in this fixture.

   Contraposition is the actual reason for failure:

   ```lean
   theorem plain_demandsMore ...
       (hc : 0 < c) (hmod : w.Models μ)
       (hpin : F.val XAY = some false)
       (hpos : 0 < mass μ (recEvent ι F))
       (hA : 0 < mass μ (ι XA ∩ recEvent ι F)) :
       ¬ DemandsNoMore ι w (plain (.strength XA XAY c))
   ```

   `contraCert` is a real conflict: `5/3` times the specialized row plus `−P(A) ≤ −1/5` yields `0 ≤ −1/5`. The stronger-row failure also matches item 133:

   ```lean
   theorem defeater_not_expressed :
     ¬ ExpressesNoMore ι settled reqDef occ.form
   ```

   The report correctly leaves exact-strength `SameRole` unproved.

   **Two prose corrections are needed.** First, `REPORT.md:135` says a satisfiable warrant cannot count its rebuttal as undefeated. The actual conclusion is only:

   ```lean
   (hmod : w.Models μ) (hc : 0 < w.c)
   (hE : E ∈ w.U) (hreb : w.A ∩ w.Y ∩ E = ∅) :
     mass μ (w.A ∩ E) = 0
   ```

   Zero antecedent mass is permitted; it does not make the requirement unsatisfiable.

   Second, the [PR description](https://github.com/A-M-Berns/alignment-workspace/pull/142) claims expression holds “exactly when” kept records equal undefeated extensions. The theorem supplies only this sufficient condition:

   ```lean
   (hc : c ≤ w.c) (hA : ι XA = w.A) (hAY : ι XAY = w.A ∩ w.Y)
   (hU : ∀ F, settleOutcome F (.strength XA XAY c) = .kept →
       recEvent ι F ∈ w.U) :
     DemandsNoMore ι w (settled (.strength XA XAY c))
   ```

   Inclusion suffices; equality and a converse are neither proved nor generally necessary.

4. **Recollection: the fixtures fit; the transport claim needs precise presentation.**

   [Recollection.lean:78](/Users/anson/hub/repos/alignment-workspace/.claude/worktrees/round-2026-11-08-content-recollection/lean/Workspace/Normativity/Contrib/Recollection.lean:78) proves the requested pullback identity:

   ```lean
   (K.pull r).Sat q ↔ r.Sat (K.push q)
   ```

   Composition is also explicit:

   ```lean
   (K.comp K').push q = K.push (K'.push q)
   (K.comp K').pull r = K'.pull (K.pull r)
   ```

   The `(1,0)` transport result is an arithmetic repackaging of exact evaluation preservation:

   ```lean
   excess (K.pull r) q = excess r (K.push q)
   ```

   `recollection_step` rewrites that equality and simplifies; `recollection_chain` genuinely invokes `affine_transport_compose`, but composes two such equalities. It supplies no independently defined metric, loss or defect comparison. The Lean comment acknowledges equality; the report should make this limitation explicit.

   The approximate result is:

   ```lean
   excess r (K.push q) ≤ excess r (K₀.push q) +
     (hi - lo) * ∑ w' ∈ B, q w'
   ```

   under coefficient bounds, nonnegative `q`, and agreement outside `B`. Slack equals failure mass only when the coefficient range has width one, as in `partial_slack`; the PR and structured summaries omit that qualification.

   The garbling answer is honest:

   ```lean
   theorem garbling_of_recollection ... :
     Garbling A (compKernel A K)
   ```

   It needs a supplied common process `A`, and constructs the old process from it. It does not prove `Sufficient E A B`, whose target is `Garbling A (refKernel E B)`. The carrier mismatch and missing Integrity connection are real. The report accurately describes `Conservation.faithful` as equality of account evaluations under transport of resolution witnesses.

   The split and abandonment claims match their statements. In particular:

   ```lean
   abandon_no_sentence :
     ¬ ∃ S', ∀ w', abandon.k w' 0 = if w' ∈ S' then 1 else 0

   abandon_half ... (h1 : q 0 + q 1 = 1) :
     (abandon.pull (atLeast (1/2))).Sat q ↔ 1/2 ≤ q 1
   ```

   Consequently, [DECISIONS.md:50](/Users/anson/hub/repos/alignment-workspace/.claude/worktrees/round-2026-11-08-content-recollection/DECISIONS.md:50) is wrong to say refinement bars every change away from a concept without an exact image. Restricting new credences to `q 1 ≥ 1/2` preserves the old half-bound despite the missing indicator image. The `9/10` commitment fails because of its bound and this particular map.

5. **Precedent: the advertised order is missing.**

   [PrecedentConstraint.lean:90](/Users/anson/hub/repos/alignment-workspace/.claude/worktrees/round-2026-11-08-content-recollection/lean/Workspace/Normativity/Contrib/PrecedentConstraint.lean:90) states:

   ```lean
   Consistent Γ ↔
     ∃ P : List (Form d) → List (Form d) → Prop,
       (∀ U V, P V U → ¬ P U V) ∧
       ∀ c ∈ Γ, ∀ U V, Beats c V U → P V U
   ```

   This requires **asymmetry only**, not transitivity or acyclicity.

   A hand counterexample is three distinct reason kinds `A,B,C`, each at strength `1/2`, with cases `A` over `B`, `B` over `C`, and `C` over `A`. Every pair passes the implemented check; no transitive strict priority order can rationalize all three. The graph’s statement that one consistent priority rationalizes the base therefore overstates the theorem (`graph/nodes/precedent.consistent-iff-pairwise.md:12`).

   The forbidden and distinguished fixtures do establish the advertised outcomes **under this weaker predicate**:

   ```lean
   ¬ Permitted [precedent] forbidden
   Permitted [precedent] distinguished
   Permitted [precedent] distinguished ∧
     Permitted [precedent] distinguishedPro ∧
     ¬ Permitted [distinguished, precedent] distinguishedPro
   ```

   “Allowed, not better” follows. The model reads survivors and constrains proposed dockets externally; it installs no new survivor rule. Its reading of undercut as outweighing is explicitly acknowledged as an assumption.

   Also narrow “a rebutted occurrence is on neither side”: `caseOf` puts **every undercut occurrence** among losers irrespective of settlement. The cited theorem establishes only the quiet-docket fixture:

   ```lean
   caseOf [pro (3/4), con (1/2)] DocketState.quiet
     ⟨![none, some false, none]⟩ =
       ⟨[Form.premise 0 (3/4)], []⟩
   ```

   Filing against item 117 is defensible as related evidence about precedent constraints. It does not deliver that item’s canonical selection rule or lock.

6. **Registry and item 134.**

   All eight records name actual theorems, not definitions. Their hypothesis packages have concrete instances; I found no vacuous registration.

   | Claim | Witness and scope assessment |
   |---|---|
   | `rows.incompatibility-entailment` | No propositional premises; feasible positive and negative entailment examples exist. Accurate; bears on 118. |
   | `seed.bound-certified` | `lowerBound_witness` applies the theorem to `defeat_widens.1`. Accurate; delivers 118’s certificate statement. |
   | `seed.forced-interval-rational` | `forcedInterval_witness` supplies a real feasible point. Accurate with nonemptiness; delivers 118’s attainment statement. |
   | `expresses.kept-row-demands-no-more` | `settled_expresses` supplies all hypotheses; `μ_models_kept` prevents semantic emptiness. Registry wording preserves the sufficient-condition scope. |
   | `expresses.entitlement-discriminates` | Closed statement: `Nonempty (...) ∧ IsEmpty (...) ∧ IsEmpty (...)`, witnessed by `entitlementW` and the two impossibility proofs. Accurate as a fixture. |
   | `expresses.plain-row-demands-more` | `plain_not_expresses` supplies positive masses and a requirement model. Accurate; bears on 113. |
   | `content.conservative-iff-image` | No propositional premises; conservative and nonconservative fixtures. Accurate for finite bundle regions and linear translations; relevant to 134. |
   | `precedent.consistent-iff-pairwise` | No propositional premises; consistent and forbidden fixtures. Its literal statement, `Consistent Γ ↔ ∀ c ∈ Γ, ∀ c' ∈ Γ, ¬ (...)`, is correct; the order interpretation is not. |

   [Item 134:49](/Users/anson/hub/repos/alignment-workspace/.claude/worktrees/round-2026-11-08-content-recollection/graph/nodes/item-134.md:49) is **not yet a sufficiently precise round specification**. A general rational translation cannot simply compose with an interpretation valued in `Finset W`: stochastic pullbacks produce fractional observables. Further, no broken row commitment does not preserve entitlement’s independent admission and live-account conditions. Specify the new interpretation carrier and the state/model-preservation hypotheses, or request a counterexample before asserting the transport theorem.

7. **Verdicts and omissions.**

   Matter 1’s **fits** is earned. Matter 2’s **fits** is earned for expression checking with declared semantics, not independent defeat semantics. Matter 3’s **fits in part** is earned with the equality-based transport and scaled-slack qualifications. Matter 4’s **fits in part** needs an explicit admission that it implements asymmetric consistency rather than the requested priority order.

   Each matter does answer “checks or chooses” and names declared inputs. The limitations section misses the order gap, trivial protocol scaffolding, the absence of a converse characterizing `U`, and the interpretation-type problem transferred to item 134.

8. **Standards and PR coordination.**

   Names are marked provisional; literature attribution is explicitly unverified rather than presented as checked. I found no new axiom declaration or substantive padding defect. The generalizations and item-117 routing are declared deviations.

   Registering conservativity against **new** item 134 also deviates from the dispatch’s **existing-item** requirement; this is not identified as a deviation. The report additionally calls item 113 “closed” at line 316 although its structured status remains `open`.

   [PR #141](https://github.com/A-M-Berns/alignment-workspace/pull/141) is open and does contain #140’s digest, so avoiding duplicate work is defensible. Preserve that digest when reconciling the branches, and resolve #142’s empty `merged` field before publication; the current site lists all digest entries as merged work. The report’s verification and review placeholders must be filled before merge; the PR description prematurely says those records already exist.

The ranked defects are:

1. **Blocking:** asymmetric consistency is presented as existence of a priority order. Add transitivity/acyclicity, or explicitly narrow the result and record the three-cycle limitation throughout the report and graph.
2. **Should-fix:** remove the PR’s false “exactly when” characterization of kept versus undefeated records.
3. **Should-fix:** make item 134 type-correct and state sufficient hypotheses for entitlement transport.
4. **Should-fix:** correct the satisfiability and abandonment overstatements, qualify rebuttal’s exclusion from cases, and retain the oscillation factor in slack summaries.
5. **Should-fix:** complete the review/verification record, correct item 113’s status description, and declare the new-item registration deviation.
6. **Note:** describe the entitlement fixture’s trivial protocol scaffolding and the transport lemma’s equality-based scope; finish digest coordination at merge.

The most important overstatement is **“one consistent priority”**: the formal predicate accepts a three-cycle.

**fix-then-merge**

The precedent interpretation currently promotes a weaker theorem as the requested order constraint. The remaining findings are scope and specification corrections; I found no corresponding mathematical defect in the conservativity, certificate-completeness or expression-discrimination proofs.