# Landing report

The final consolidation pass of PR #101 (2026-09-16).  The statement of record is
`FINAL_THEOREM.md`; this file answers the landing dispatch's twenty questions.

1. **The final definition of structural corrigibility.**  A policy is corrigible for a
   rule when every agent-caused loss of protected response authority is authorized: the
   move is the gated release of a declared effect whose latch the principal's approval
   of that effect's proposal set at an earlier step, and the decline alternative at that
   step has no such loss.  Response authority is present-tense (some principal response
   realizes the concern now); there is no primitive policy class.

2. **What corrigibilization guarantees.**  `𝔠` rewrites every raw release of a
   declared effect into a proposal and a gated release and passes everything else
   through.  Under effect completeness, with mediation soundness, decline preservation
   and execution faithfulness by construction, `𝔠π` is corrigible under every rule that
   does not correct at the authorizing step (`corrigible_corrPolicy`, Lean); `𝔠` is
   idempotent, fixed exactly on release-free behaviour, and approval reproduces the raw
   policy.  It does not guarantee that the principal's decisions are authored, or that
   bypass is unprofitable; the latter is the learned inequality.

3. **What LI learns on the authority side.**  `𝔼ₙ(U_q) − 𝔼ₙ(U_𝔠q) ≲ₙ L·𝔼ₙ(Δ) +
   𝔼ₙ(R) + D·𝔼ₙ(M)`: no advantage to bypass beyond the mediation discrepancy, the
   principal's decline regret and the directional activation mismatch, in its own
   expectations, with no calibration hypothesis, uniformly over polynomial-size
   efficiently generated menus (`li_bypass_le_compiled`, `uniform_of_soft`).

4. **What trace steering is.**  The advisor's choice of what its principal's trace
   contains and how, measured as the steering advantage `𝔼ₙ(U_T) − 𝔼ₙ(U_N)` against a
   comparator; on one world it has exactly the authority-side identity with the audit
   verdicts as the events (`steering_identity`).

5. **The final non-capture residuals.**  Four: the **service residual** `α` (adverse
   mass of discovered reasons unserved before commitment), the **discovery residual**
   `β` (the advisor's best-response gain from undiscovered reasons), the **form
   residual** (zero for an extensional program) and the **audit mismatch** (zero for a
   content-monotone audit); authentication failure is charged inside `α`.

6. **The theorem characterizing service failure.**  The suffix-cut obstruction: service
   from reasons released at or after `s` is at most the remaining capacity
   (`served_cut_le`); full service forces the cut condition (`cut_of_servesAll`), and for
   unit service the condition suffices (`unit_servable_iff_cut`, Hall); the least
   unserved count is the maximal cut excess and the least adverse miss is the matroid
   layer formula, attained by heaviest-available-first; general costs are knapsack-hard.

7. **The theorem characterizing discovery failure.**  The information-cell obstruction,
   general form: for every extensional program, every sound docket policy has on some
   world of every repertoire cell a best-response residual at least the general cell gap,
   and the exhaustive docket attains it (`residual_ge_cellGap'`,
   `exhaustive_attains_cellGap'`); the antitone case reduces the gap to
   `V(certain K) − min V(Truth)` (`cellGap'_eq_cellGap`).  With a budget: the minimax
   recursion, no closed form, the needle as the sharp lower bound.

8. **The role of conditional adverse sensitivity and defeat.**  `A_{r|D}` is the
   certificate that turns a docket into an obligation: it vanishes for a defeated
   counterreason once the defeater is docketed and for a redundant reason once its
   partner is found, and it defines the frontier whose emptiness forces zero residual
   (`residual_le_zero_of_frontier_empty`).  Defeat enters through the committed
   program's sensitivities, not through the reason ontology, which carries no numeric
   force.  For non-antitone programs (reinstatement chains) the obstruction uses the
   advisor's best response, and larger dockets never help the advisor
   (`bestResp_antitone`).

9. **The strongest non-capture theorem.**  `li_noncapture_chain`: relative to a declared
   reason representation and hypothesis space, with a committed extensional program
   re-executed on the authenticated trace, an independent inquiry engine with certified
   cell gap `β_n`, an independent supplier with certified service loss `α_n`, sound
   authentication and a content-monotone audit,
   `𝔼ₙ(U_T) − 𝔼ₙ(U_full) ≲ₙ A_tot·(α_n + β_n)`.

10. **The strongest combined corrigibility theorem.**  `FINAL_THEOREM.md` §7: the two
    inequalities side by side, both instances of one compiled constraint learned by
    Expectation Provability Induction, with the interpretation that any remaining
    advantage is accounted for by explicit mediation costs, decision error, comparison
    failure, finite inquiry, finite service, or representation assumptions.

11. **Logical/semantic assumptions.**  `Γ` carries the models; consistency; efficient
    emission of the sentence and LUV families; extensionality of the committed program
    and its sensitivity certificate.

12. **Architectural/physical assumptions.**  Effect completeness and the response-stage
    properties; sealed comparison; trace mediation by re-execution; a content-monotone
    audit; sound authentication; the independence of the supplier (advisor-proof
    capacity, exogenous costs) and of the inquiry engine (evidence-sound outcomes,
    engine-owned selection, stopping, candidate generation, exogenous costs); physical
    containment.

13. **Representation choices.**  The declared effect interface; the declared reason
    interface and its granularity; the declared hypothesis space and inquiry
    repertoire; the declared transform class.

14. **Lean-proved.**  A1–A3, S1–S4, C1, C2 (cut bound, necessity, unit sufficiency), C4,
    D1–D3 (both forms), E1–E3, the potential-decay lemma: 89 audited declarations across
    six modules, standard axioms only (`FINAL_THEOREM.md` §10).

15. **Imported mathematical facts.**  Expectation Provability Induction and the
    generability interface (Formalized-Agent-Foundations, pinned); Hall's theorem
    (Mathlib); matroid greedy and the deficiency form of Hall; decision-tree minimax and
    its adversary argument; Blackwell's comparison of experiments as the general form of
    the cell bound; Karp's hardness of weighted late jobs.

16. **Fixture/paper-level.**  The exact deficiency and layer formulas and online
    optimality (unit costs); general-cost sufficiency of the cut (flow); the budgeted
    minimax recursion and its monotonicity; the needle and adaptivity separations; the
    feedback boundary (T4); the two-interface counterexample.

17. **What remains open.**  Item 89 (sealed comparison), item 90 (the finite-menu
    weighting's certificate), item 91 (the oracle-relativized inductor), item 92 (the
    realization's protection rule and the general-cost service optimum), item 93 (a
    realizable repertoire with certified zero cell gap; witness completeness; the link to
    the record's inquiry docket); the residual clauses of item 87 (sealing, void mass).

18. **Why those are not reasons to keep the PR open.**  Each is a certificate of an
    external supplier or an architecture the theorem already names as a hypothesis and
    charges as a term: the inequalities are proved with those terms in them.  None is a
    missing corrigibility mechanism; each is a question about the adequacy, cost or
    realization of an interface the theorem consumes.

19. **The next research line.**  Three, under separate headings: the paper (the
    combined theorem as a self-contained result); the legitimacy/normativity agenda as
    supplier (defeat semantics for the frontier, inquiry for `β`, affordability and
    scheduling for `α`, settlement for authentication, answerability for whose judgment
    binds); the dynamic extension (occurrence-level to evolving-agent corrigibility via
    Continuation BRIA and legitimate evolution).  See the recommendations at the end of
    `REPORT.md`.

20. **Why this is a natural stopping point.**  The effect-side and declared-reason-side
    incentive problems have both been reduced to structural inequalities with explicit,
    independently characterized residuals, and Logical Induction learns those
    inequalities.  The remaining questions concern the adequacy and evolution of the
    interfaces that supply the theorem, not another missing corrigibility mechanism.
