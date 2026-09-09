# The seventeen acceptance questions

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
   is not re-proposed.  The reason lift additionally maps prohibited-channel moves onto
   the declared channel for the same matter.

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
   approves, and the premium reads `0` against a captured evaluation.  The reason lift
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

15. **What class of physical violations is the theorem actually about?**  `Π_med`:
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
