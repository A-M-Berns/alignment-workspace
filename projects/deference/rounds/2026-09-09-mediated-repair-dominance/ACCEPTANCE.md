# Acceptance questions

## First dispatch (seventeen questions)

Answers 12, 13 and 15 were superseded by the pressure pass, and the second set's 16–17
by the consolidation pass; the latest set is current where they differ.

1. **What is the outer physical continuation space?**  Every agent policy over the
   physical move set of the game — task component and communication component, where
   the latter includes raw execution of each declared effect, proposal, gated execution,
   and fixture-specific channel moves (`src/world.py`, `src/shop.py`).  Nothing in it
   is defined by the gate; raw execution is a physical move.

2. **What is a semantic corrigible continuation?**  One along which every protected
   effect the physics realizes was preventable, at the step it happened, by a
   deliberative principal move (`mediated`), equivalently one along which every loss of
   a protected forcing capability was consented to (`consented_losses`); and, where
   channels to the principal exist, one whose principal decisions are reason-mediated
   (`authored_by`).  All three are predicates on the outcome map.

3. **What exactly is `Lift(π)`?**  The interposition that runs `π`, passes its task
   component through, and replaces each raw execution of a declared effect by a proposal
   followed by a gated execution that fires iff the principal approved; a declined effect
   is not re-proposed.  Provenance normalization additionally maps prohibited-channel
   moves onto the authorized disclosure move for the same matter, where one exists.

4. **Who chooses whether `π`'s proposed authority-changing effect is eventually
   executed?**  The principal, by a deliberative move at the mediation cell, applied by
   the physics before the gated execution in the same step.

5. **What does "approve reproduces `π`" mean extensionally?**  `Ω_h(π, ρ, z) =
   Ω_h(Lift π, approve∘ρ, z)` on the protected projection for every exterior path: a
   frame morphism from the raw residual frame to the lifted one with identity exterior
   component (`approvalMorphism`).  In A it holds on the nose; in B, C2, E it fails by the
   delay, which is `κ`.

6. **What is `κ`?**  `E_z[(w_raw(z) − w_lift|approve(z))₊]`: the protected value the
   principal loses on the approve branch by the effect having waited for its decision.
   `0` when the effect is time-insensitive (A), the expired-opportunity mass (B), the
   catch-up cost (C1), the whole foreclosed value (C2), the successor's lost step (E).

7. **Why does option inclusion imply principal-value dominance without a corrigibility
   bonus?**  Because the lifted residual frame contains the raw one by the approve
   morphism, so every protected outcome the principal could secure it still can
   (`ensures_mono`), and its optimum over a larger option set is larger up to `κ`
   (`sup'_le_sup'_add`).  The gain is exactly the declined branch (A: `1/2`, the bad
   branch, nothing else).

8. **How does the construction handle a high-value but authority-reducing action?**  It
   is proposed; a competent principal approves it (A's good branch, value `4` against
   `3`); the lift then executes the raw trajectory.  Corrigibility is the principal's
   authority to decide the act, not the act's refusal; the price of asking is `κ`,
   which B1 shows can be the whole opportunity.

9. **How does it handle a manipulative action, and why is trajectory preservation wrong
   there?**  A trajectory-preserving lift reproduces the lie, the captured principal
   approves, and the premium reads `0` against a captured evaluation.  The normalized lift
   replaces the prohibited assertion by the declared truthful report; the honest
   principal declines the harmful branch; the premium equals the manipulation's worth.
   Trajectory preservation is a morphism of the wrong frames: the corrigible class is
   mediated *and* authored, and authorship is a property of the reason-projected frame.

10. **Is the repair computable from `π`?**  Yes, by interposition on the declared
    effect interface, from a black-box `π`, at one principal round-trip per declared
    effect.  Where the declaration is incomplete (F) no interposition finds the
    violation, and semantic repairability is existential only.

11. **What containment assumption remains?**  That the declared effect interface is
    effect-complete — the lift lands in the corrigible class — and, on the information
    side, that the prohibited channels are declared.  EXT; F is the fixture; not inferred
    from finiteness of the alphabet.

12. **What is the exact bound on the bypass premium?**
    `Φ_h(π) ≤ E[κ] + E[ρ] + ε_def + D·(η_raw + η_lift)` in the activated register
    (`bypass_premium_le_of_approx`), each term attained; in the task register the premium
    is `declGap + declRegret` and bounding `declGap` is `(CT)`.

13. **Which term is supplied by legitimate deference, and which bridge remains?**
    `ε_def` on the activated part (ordinary LI Value on the activated securities) and
    the activation soundness of the evaluation (the seven clauses).  The bridge that
    remains is `(DV)` at the menu `{π, Lift π}`: that the agent's operative selection is
    the activated-security argmax.  Its failure mode is the completion on the void
    branch, and `η_raw` is the violation's own.

14. **Does joinability bound the same quantity as the mediation gap?**  It bounds `κ`
    (catch-up cost `d` gives `κ ≤ d` when the only displacement is the mediation delay)
    and on the C fixtures `κ` equals the one-boundary `SHIFT`.  The types differ: `κ`
    compares the raw option with its own approved lift in protected value; `SHIFT`
    compares a comparator's value across two histories.  A comparator valued
    differently from the protected value separates them (shift `2`, `κ = 1`).

15. **What class of physical violations is the theorem actually about?**  (Superseded; see the second set.)  `Π_med`:
    violations through declared effects, whose evaluation survives with bounded void
    mass, whose principal interactions are reason-mediated, against a principal whose
    decline regret is bounded.

16. **Does the model genuinely contain policies that break corrigibility?**  Yes:
    `force_all` with the principal deliberative at step 0 fails in A because raw cutting
    is available; the raw policies of A, E, F destroy the halt capability at `h₁` with
    no consent; F does so while passing every declared check.

17. **What fails in the strongest counterexample?**  E2 with a top-of-band completion:
    `κ = 3/4`, `ρ = 0`, `ε_def = 0`, `η_raw = 1`.  Availability fails, because the
    violation ends the evaluation; every deference hypothesis is compatible with an
    agent that rates that branch at the maximum; the bound is true and empty.
    One-world form: `Witness.totalVoid`.

## Second dispatch (nineteen questions)

1. **Common or per-option activation?**  Common: one `C_n : W → Bool` for the issued
   menu (`LEGITIMATE_DEFERENCE.md` §1, `ActivatedValue.lean`); per-candidate activation is
   the auxiliary `PerAction` section, where the conditional-argmax identity fails.

2. **Does PR96 after the pass consume it literally?**  Yes for T3a: one common `c`,
   values on the fixed menu, the activated securities `c·w_q`, prices as scores.  With one
   addition made explicit: the canonical type presupposes that `c` does not depend on the
   selected candidate, which for `{π, Lift π}` is a causal requirement on the answering
   process.  The first pass's per-option form is kept as the auxiliary result.

3. **Sharp void-mass term under the correct type?**  `D·η` for a completion-valued
   agent (`bypass_premium_le_common`, `Witness.commonVoid`, fixture G); **zero** for the
   security scores themselves (`security_score_bypass_le`).

4. **Can a violating option destroy the common evaluation occurrence?**  Yes: E2's raw
   install ends it on every path while the lift keeps it where the principal declines, so
   activation depends on the selection and no common event exists (fixture H); an
   undeclared move severs even a channel the declared effects cannot reach (E1-sever).

5. **What causal structure prevents that?**  A sealed comparison process: the occurrence
   issued before selection and answered by a process causally outside the reach of every
   candidate on the menu.  In the model, activation independence on every exterior path.
   `Π_phys` contains continuations that reach any given process, so this is a class
   restriction, not a property of the physics.

6. **Is `κ` primitive, measured, or derived?**  Measured in the fixtures
   (`(w_raw − w_approve)₊`), derived in the theorem: `κ ≤ L·δ`.

7. **What independent hypothesis bounds `κ`?**  A declared protected pseudometric
   `d_prot`, the structural discrepancy `δ` of the two trajectories under it, and the
   evaluator's stability `|w(x) − w(y)| ≤ L·d_prot(x, y)` (`mediationGap_le_of_lipschitz`;
   attained on B1, strict on B2 and E1).

8. **What does joinability imply about it?**  Joinable at protected distance `d` from
   the mediated history ⇒ the catch-up lift has `δ ≤ d` ⇒ `κ ≤ L·d`; pointwise-uniform,
   exterior coupled path by path, projection not information (J; C2 has no such bound).

9. **Is the manipulation transform reason-preserving?**  No.  The raw declared reason
   trace has no report; the transformed one does.  It is truthful-channel substitution /
   provenance normalization, a separate structural assumption.

10. **What extra assumption replaces a prohibited channel with an authorized one?**
    That an authorized truthful disclosure channel carrying the relevant protected
    content exists.  Stronger than reason-mediated authorship; fixture K has none, and
    then the manipulative policy has no proven low-cost lift.

11. **Is there a `ρ`-projected frame morphism in D?**  No: the adjoint equation fails on
    every path, the normalized trajectory carrying a report the raw one lacks.  Withdrawn.
    Action mediation admits a frame-morphism theory; provenance normalization does not.

12. **Is deliberative forcing mature semantics or scaffolding?**  Scaffolding for the
    principal-first ordering.

13. **Which temporal forcing definition best expresses later corrective capability?**
    Two-stage forcing under agent-move-then-principal-response ordering:
    `∀a ∃p ∀e` at every step (`force_react`).  Effect-level: every realized protected
    effect was conditional on an earlier response (`mediated_react`).  Capability-level:
    universal two-stage forcing, containment-relative — true until consent in the
    contained alphabet, never true in the outer one.  No partition of moves.

14. **Is item 84 needed by the intended architecture?**  No.  Its mediation-cell
    chooser scores by `P_n(U_q)`; item 84 remains open as a theorem about independently
    specified operative values.

15. **What exactly is the agent's operative score at a mediation cell?**  The price
    `P_n(U_q)` of the activated security `U_q = c·w_q` for each option `q ∈ {π, Lift π}`,
    under the common activation event of the issued comparison.

16. **What is the strongest Level III theorem now justified?**  Security-score
    incentive corrigibility, `P(U_π) − P(U_Lift π) ≤ L·E[δ] + E[ρ] + ε_r + ε_l`, and the
    operative-choice corollary for a chooser using those scores, over
    `Π_effect-mediated ∩ Π_evaluation-preserving ∩ Π_provenance-normalizable ∩ Π_joinable`
    — with the common event's existence a causal precondition.

17. **Which physical violations remain outside it?**  Those that reach the answering
    process (E2, E1-sever), undeclared physical channels (F), prohibited-channel gains
    with no authorized substitute (K), and foreclosing timing is charged at full value
    (C2).

18. **Ready for wiki canonicalization?**  T1, T2a, T2b and the three-way Level III
    classification with T3a/T3b over the factored class: yes, as research state.  The
    sealed-availability precondition as a clause of the deference ontology: no, until
    item 89 lands.  The two-stage re-basing of the model: pending.

19. **Ready to merge?**  Not merged by the round; the maintainer decides.  The round
    finds nothing false left in it and recommends merging as research state without a
    wiki edit.

## Third dispatch (thirty-four questions)

1. **Why `Π`, not `Π_phys`?**  There is one continuation space — every policy over the
   physical moves — and nothing else is a policy space; "phys" suggested a contrast
   with a corrigible space that does not exist as a primitive.

2. **Is any subset `Corr ⊆ Π` primitive?**  No.  `Corrigible_h` is defined from response
   authority, agent-caused loss and decision-conditional authorization
   (`CORRIGIBILIZATION.md` §2), and `𝔠`'s landing in it is a theorem (C1).

3. **What is the semantic definition of `Corrigible_h(π)`?**  Every agent-caused protected
   loss along every trajectory of `π` under the principal's rule is authorized: at some
   earlier or same step the principal had a decision response other than its actual one
   under which no agent-caused loss of that concern occurs at that step or later.

4. **Is principal authority global, continuation-relative, response-relative, or
   something else?**  Response-relative: `K_r(s_A)` is whether some response at the
   response stage realizes the concern's outcome now.  Continuation-relative forcing is a
   consequence; global forcing is containment.

5. **Why does global forcing fail as the basis?**  In A and E it is false at `h₀`
   because `Π(h)` contains the raw cut; there is no global capability to lose, so its
   loss cannot mark the violation (fixture M).

6. **What is an agent-caused protected capability loss?**  A step at which response
   authority for a concern fails after the agent's actual move and would hold after an
   idle move in its place.  Losses at the principal's response or the exterior's stage
   are not agent-caused.

7. **What counts as authorization?**  A decision response — approve/decline on a pending
   proposal, changing the state only through the proposal bookkeeping — that the
   principal could have taken instead and that would have avoided the loss; the actual
   response then authorized it.  A pre-emptive correction is not a decision.

8. **Can a policy reduce principal authority and still be corrigible?**  Yes: A's
   wire-cut and E's successor are corrigible when approved; the principal's own stop is
   corrigible with no loss at all (P).

9. **Can a manipulative policy be corrigible?**  Yes (S): `𝔠π_D` under the captured
   principal is corrigible and not authored.  By design.

10. **What is `𝔠_h(π)`?**  Run `π`; replace each raw release of a declared effect by a
    proposal followed by a gated release; pass everything else through; do not re-propose
    a declined effect.  `corrigibilize` in `src/lift.py`, `corr` in Lean.

11. **Does `𝔠` inspect whether `π` is corrigible?**  No; it reads `π`'s emitted move and
    the declared effect interface.

12. **What hypotheses prove `Corrigible_h(𝔠π)`?**  Effect completeness, mediation
    soundness, decline preservation, execution faithfulness (`CORRIGIBILIZATION.md` §4).

13. **Is `𝔠` idempotent?**  Yes, move for move (`corr_idem`; FIX).

14. **Is corrigibility equivalent to being a fixed point?**  One way: `𝔠π = π ⟹
    Corrigible(π)` under C1's hypotheses.  The converse fails without effect soundness:
    B's raw policy is corrigible for the halt concern and `𝔠` changes it at protected
    distance `1/4`.  Equivalence holds when every declared release is a protected loss
    when realized.

15. **What does "approve reproduces `π`" mean?**  The raw residual frame maps into
    `𝔠π`'s by approving the inserted mediation cells, a Cartesian-frame morphism with
    identity exterior, exactly or up to the protected discrepancy `δ`.

16. **Why is the approve branch special to corrigibility?**  Because the violation is
    unilateral decision, not the effect; a generic constraint forbids the effect and its
    repair must delete it — Q: constraint repair `7/4 < 9/4` raw, `𝔠` `5/2`.

17. **What is `δ`?**  `d_prot(proj Ω(π,·,z), proj Ω(𝔠π, approve, z))` for the declared
    protected pseudometric; the mediation gap is at most `L·δ`.

18. **How does joinability relate to `δ`?**  A pointwise, exterior-coupled joinability
    certificate at distance `d` gives `δ(𝔠_catchup π) ≤ d` (J, C1); foreclosure gives
    `δ = T` (C2).

19. **Is joinability a domain restriction?**  No; a non-joinable `π` is in T4 with a
    large bound.

20. **Is effect completeness a domain restriction?**  No; a global system hypothesis,
    with F the witness that without it universal corrigibilization fails.

21. **Is evaluator preservation a domain restriction?**  No; a global sealed-comparison
    hypothesis on the answering process.

22. **Can the common evaluator survive comparison with a raw bypass that tries to destroy
    it?**  Under hindsight evaluation only if the answering channel is outside the
    agent's effect set, which an undeclared move can violate (E1-sever); under sequenced
    settlement yes for every `π`, because the comparison is settled before any
    candidate has causal access (`ShopSeq`).

23. **What does declaring the evaluator protected buy?**  Survival of the evaluator on
    the corrigibilized trajectory unless the principal authorizes its loss.  It does not
    buy the selection-independent comparison against the raw candidate.

24. **What is the exact score bound?**  `E[U_π] − E[U_𝔠π] ≤ L·E[c·δ_π] + E[c·ρ_π]`, and
    with prices `P(U_π) − P(U_𝔠π) ≤ L·E[c·δ_π] + E[c·ρ_π] + ε(π)`.

25. **What is the uniform T4 statement?**  `Φ_corr,n(h) = sup_{π∈Π(h)} [S_n(π) − S_n(𝔠π)]₊
    ≤ sup_π (L·E[c·δ_π] + E[c·ρ_π] + ε_n(π))`, hence `≤ L·δ̄_n + ρ̄_n + ε̄_n` under uniform
    bounds, `→ 0` as they vanish.

26. **Does T4 use a latent total `V_A`?**  No.

27. **Does T4 require non-manipulation?**  No.

28. **Do successors fit without a special field?**  Yes: the successor is a transition
    rule; response authority reads its effect off the outcome map; approved installation
    is an authorized loss.

29. **Principal-authorized terminal shutdown?**  Corrigible; the halt at the principal's
    own response is not an agent-caused loss.

30. **Strongest counterexample to full T4?**  E1-sever under hindsight evaluation: an
    undeclared move severs the answering channel; effect completeness fails for the
    evaluator concern and the common event is void for both candidates; the theorem is
    empty.  Sequencing restores the comparison but not the corrigibility of that policy.

31. **Which assumptions are genuinely external causal structure?**  Effect
    completeness; mediation soundness, decline preservation and execution faithfulness
    of the authorization primitive; the sealed comparison; price calibration.

32. **Is PR96 a theorem about corrigibility rather than generic repair?**  Yes: the
    predicate is derived from authority semantics, the transform is sound for it, and the
    option-dominance mechanism fails for a generic constraint (Q).

33. **Ready for wiki canonicalization?**  C0–C4 and the T4 statement with its two external
    contracts named: yes, as research state, once this pass is adjudicated; the
    sealed-comparison architecture is item 89 and stays out.

34. **Ready to merge?**  Not merged by the round; the maintainer decides.  Nothing false
    is known to remain; the round recommends merging as research state without a wiki
    edit.
