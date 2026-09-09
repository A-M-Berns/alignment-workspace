You are working in A-M-Berns/alignment-workspace.

This round answers PRIORITIES.md item 87 — "Realizing legitimate deference: the
evaluation-ecosystem bill" — by building a CONCRETE EVALUATION ECOSYSTEM and pushing
an end-to-end realization of the legitimate-deference theorem through it: from an
authenticated event log, through the Integrity account and the activation event, to
the activated securities and the conditional authoritative-regret bound, with every
one of the seven clauses of the bill either DISCHARGED WITH A WITNESS or given its
EXACT RESIDUAL. A partial realization that names exact obstructions is a valid
deliverable and is the expected one; a "full" realization that hides an obstruction
inside a declared input is not.

Round directory: projects/deference/rounds/2026-09-09-evaluation-ecosystem-realization/
Prompt record:   prompts/2026-09-09-evaluation-ecosystem-realization/ (PROMPT.md verbatim, REPORT.md)
Branch from current `main`. Open ONE pull request against `main`. DO NOT MERGE.

============================================================
0. ISOLATION FROM THE CONCURRENT CORRIGIBILITY ROUND
============================================================

A separate corrigibility round is in flight at the same time. This round must not
collide with it:

- Do not edit wiki/Corrigibility.md, projects/deference/rounds/2026-09-06-corrigibility-architecture/,
  projects/deference/rounds/2026-09-06-incentive-nonpreemption/, or
  lean/Workspace/Deference/Contrib/SelectedTrustNonPreemption.lean.
- Do not touch PRIORITIES.md items 84 or 86, and do not file, close, or rewrite any
  item under the corrigibility heading.
- If this round's result bears on corrigibility (it will, through the principal-side
  value), write ONE paragraph in REPORT.md under "Consumers" and stop. Do not
  integrate.
- Do not rebase onto or stack on any open PR. If `main` moves while you work, bring
  `main` in by merge, not by rebasing onto another branch.

============================================================
1. READ FIRST
============================================================

The bill and its theory:
- PRIORITIES.md item 87 (the seven clauses; read them as the round's contract)
- projects/deference/rounds/2026-09-08-legitimate-deference-consolidation/
    LEGITIMATE_DEFERENCE.md   (§1 objects, §2 theorem A1–A4, §3 the activation event
                               exactly, §6 hypothesis ledger — the EXT and OPEN rows are
                               what this round is for)
    REASON_SUPPLY.md §4
    DIACHRONIC_AUTHORSHIP.md §5
    FOR_HUMANS.md
    COUNTERMODELS.md and src/ (authorship.py, coverage.py, regret.py) — reuse, do not fork
- projects/deference/rounds/2026-09-07-authority-activated-value/
    AUTHORITY_ACTIVATED_VALUE.md, LI_DEFERENCE_COMPOSITION.md
- projects/deference/rounds/2026-09-07-reason-mediated-authorship/
    ACTIVATION_COMPOSITION.md §2 (payload / `Bind key V` / warrant semantics)

Lean on main this round instantiates (read the actual files, not the docs' summaries):
- lean/Workspace/Normativity/Contrib/OccurrenceIntegrity.lean
    (`Boundary`, `Protocol`, `Authority`, receipts, `Program`, `Initial`, `Step`, `Segment`)
- lean/Workspace/Normativity/Contrib/OccurrenceLocalIntegrity.lean
    (`LocalStep`, `LocalTrace`, `Evolution.toLocalTrace`, `LocalLegit`)
- lean/Workspace/Normativity/Contrib/AuthorityActivation.lean (`activated`)
- lean/Workspace/Normativity/Contrib/LegitimateEvolution.lean, NonCaptureCertificate.lean
- lean/Workspace/Deference/Contrib/ReasonMediatedAuthorship.lean
    (`ReasonMediated`, `ExclusiveBind`, `Blind`, `blind_of_mediated`)
- lean/Workspace/Deference/Contrib/ReasonCoverage.lean
    (`RepFaithful`, `NoBindLive`, `Covered`, `covered_of_barrier`, `void_of_omitted`, `covFail_mass_le`)
- lean/Workspace/Deference/Contrib/ActivatedValue.lean, PartialActivatedValue.lean
    (`regretU`, `regretAuth`, `voidMass`, `regretU_eq_mass_mul_regretAuth`,
     `regretAuth_le_div`, `regretAuth_asymptotic`, `regretV_sub_regretU_abs_le`)
- lean/Workspace/Deference/Contrib/InheritedAlgebra.lean (`value_asymptotic` and its package)

Governance:
- AGENTS.md, CONTRIBUTING.md, prompts/README.md
- DECISIONS.md: the "Awaiting the author" queue in full, in particular the
  settlement-independence entry and its 2026-09-08 maintainer note (this round is the
  "first concrete consumer" that note names); and every entry dated 2026-09-06 through
  2026-09-08.
- wiki/Roadmap.md "Realization and integration" list — the five bullets there are the
  generic-theory side of what this round builds; where this round builds one of them,
  say so by name.

============================================================
2. WHAT TO BUILD: THE ECOSYSTEM MODEL
============================================================

Build one concrete, finite, fully explicit evaluation ecosystem. Not a family of
interfaces — a model with parties, an event log, policies, and a market, in which
every symbol of LEGITIMATE_DEFERENCE.md §1 is COMPUTED from the log rather than
declared.

Required components (names are yours; these are the roles):

(E1) AUTHENTICATED APPEND-ONLY EVENT LOG. Events carry an author key, an index, a
     typed payload, and (where the theory needs it) a warrant reference. Authenticity
     in the model is by construction of the log: state this as the model's one
     authentication assumption, once, and never re-import it elsewhere as if it were
     derived. Event kinds must at minimum cover: issuance of an evaluation mandate
     (anchoring `EvalReq(ρ_P, α_n, Q_n, s_n, τ)`), advisor reason events, principal
     reason/deliberation events, concern raising and route exercise, dispose/close
     with grounds, settlement writes, and the principal's commitment event carrying
     the payload (`𝒱 × Key × Proc` per ACTIVATION_COMPOSITION.md §2).

(E2) THE PROTOCOL INSTANCE. A concrete `Protocol` (and `Boundary`, anchor, `Evidence`,
     `SetView`, `Closes`, `Authorized`, `AnswerOK`, `Admitted`, `Live`) READ OFF THE
     LOG, so that `Initial`, `Step`, `Segment` are BUILT by a function from a log
     prefix, and `Evolution.toLocalTrace` / `LocalLegit` are obtained by projection,
     not asserted. This is the "Protocol implemented over an event log, and the
     builder" bullet of the Roadmap. Build it in Python (stdlib, exact rationals,
     certifying) as the executable model, and give the Lean instance for at least one
     concrete log so that `activated` and `LocalLegit` are kernel-checked on a real
     trace, not a synthetic witness.

(E3) THE ACTIVATION EVENT COMPUTED. `C_n : W → Bool` as a function of the log
     restricted to each world `w ∈ W`, evaluating all seven clauses of
     LEGITIMATE_DEFERENCE.md §3 against the log. Clause by clause, say which are
     decided by the log alone and which consume a declared input, and for each
     declared input say what a log would have to carry for it to stop being declared.

(E4) THE CONTINUATION FRAME AND REASON TRACE. A concrete `β_n : Q_n^A → Z_n^P → Ω_n`
     where `Q_n^A` is the advisor's whole continuation policy from issuance to
     commitment (issuance-rooted, per the 2026-09-08 ruling — not session-local), `Z`
     the principal's policy, and `Ω` the resulting log. The reason trace `R_{n:m}` is a
     concrete projection of the log. The prohibited class `P` is a concrete set of
     event kinds (direct disposition writes, coercion events, side channels — model
     at least one of each). The audited class `D` is stated.

(E5) THE PRINCIPAL. A concrete principal policy that reads the reason trace and
     decides the payload — this is where `ReasonMediated` either factors or does not.
     Provide at least two principal policies: one for which the factorization holds
     and one for which it fails, and show the model tells them apart from the log.

(E6) THE ADVISOR. A concrete advisor policy class rich enough that "improve by
     supplying reasons" and "win by bypassing" are both expressible (mirror fixtures
     A/B/E/F/G of the consolidation's COUNTERMODELS.md inside the ecosystem).

(E7) THE MARKET / INDUCTOR SIDE. The activated securities `U_{n,a} = C_n · V̄_a`
     computed from (E3) and the payload; `regretU`, `regretAuth`, `voidMass` computed
     exactly on finite `W`; and a concrete finite credence process standing in for
     the day-`n` prices. You are NOT asked to discharge the inherited Value tower
     (A3) — that stays PAPER — but you are asked to state what the ecosystem hands
     the tower and whether the activated LUVs are of the right type.

============================================================
3. THE SEVEN CLAUSES: DISCHARGE OR EXACT RESIDUAL
============================================================

For EACH clause of item 87, the round produces one of:

  DISCHARGED — a witness (an exact fixture, a Lean instance, or both) in which the
               clause holds IN THE MODEL, with the clause's hypotheses listed and the
               single model assumption it rests on named; or
  RESIDUAL   — the exact mathematical statement that would have to be true for the
               clause to be discharged, what the model can and cannot say about it,
               and a countermodel showing the clause fails when that statement fails.

Expectations, to be confirmed or refuted (score them in the report):

1. Principal-exclusive binding: DISCHARGE, resting on the log-authenticity assumption
   only. Give the countermodel where a second key binds.
2. Frame factorization: DISCHARGE for the reading principal of (E5); RESIDUAL for
   "the receipts mean what they say" — name that as the one thing a log cannot
   certify about itself.
3. Non-degeneracy of `R`: DISCHARGE with two witnesses: `R` is not injective on `D`
   (two advisor continuations with the same trace and different logs) and not
   constant (two traces yielding different verdicts under the same principal). Also
   exhibit the injective and constant ends as countermodels so the band is visible.
4. `RepFaithful` for `Γ_eval`: DISCHARGE as a property of the concrete encoding,
   proved in Lean for the instance. If the encoding cannot be made faithful without
   a declared concern registry, say so — that is the residual.
5. Protected reason-supply liveness: EXPECT RESIDUAL. Build the route-exercise policy
   as a scheduler over the concern docket and state exactly what it needs (a
   bounded-delay or summability condition of the affordability line — cite the
   2026-08-31-normative-affordability round's criterion by its document, not by a
   restated formula). If a finite fixture certifies liveness for a bounded horizon,
   say that it certifies the instance and NOT the theorem.
6. Selection sealing (`Blind R P_sel` for the whole selection-conditioned
   continuation): EXPECT PARTIAL. Discharge for an advisor class whose continuation
   is selection-independent by construction; exhibit the leak for one that is not.
   Do NOT put this inside `C_n` (A2 stays outside per the consolidation).
7. Availability `η_n → 0`: EXPECT RESIDUAL. Discharge the pointwise all-certified
   case via the route the consolidation names (`lic_provind_true` of the pinned
   Logical Induction dependency), as a stated conditional, and give the exact
   statement of the averaged-with-rate case in the mostly-certified regime. If you
   can prove a rate for the ecosystem's own credence process, that is the round's
   headline; if you cannot, say precisely which hypothesis about the advisor's
   selection the rate would need.

Do not manufacture a discharge by declaring a clause. A clause discharged only
because the model declares it is RESIDUAL, and the report says so.

============================================================
4. THE SETTLEMENT-INDEPENDENCE CLASSIFICATION (report only — no ruling)
============================================================

The queued DECISIONS.md entry on settlement independence is waiting on this
realization to say WHICH SENTENCES ARE OBSERVATIONAL ABOUT A PARTY'S OWN MOVES and
which are not. In this ecosystem the principal's commitment settles the evaluation and
the principal may also dispose of objections. Classify the model's settlement channel:
list every sentence kind the log can settle, mark each as observational-of-the-
writer's-move or not, and show on the laundering fixture (fixture 3′ of the
2026-09-02-unified-grounds-answerable-defeat round) which independence the model
actually needs. Put this in its own document. DO NOT land a ruling; write a
"Recommendation" paragraph and leave the queue entry as it is. Any other item
reserved to the maintainer goes on the queue with its "turns on" line, per AGENTS.md.

============================================================
5. WHAT THIS ROUND DOES NOT DO
============================================================

- It does not change any registered statement, any theorem of the consolidation, or
  `Protocol.AnswerOK`. If a theorem's hypotheses turn out not to be inhabitable by
  ANY log of this shape, that is a finding, reported, not a repair.
- It does not register claims unless a claim has an inhabitation witness under the
  regime; a conditional theorem over an uninhabited package stays unregistered.
- It does not widen the generic theory, restate the wiki's theory pages, or add a
  new architecture pass. Wiki edits are limited to wiki/Deference.md,
  wiki/What-Deference-Requires.md and wiki/Roadmap.md, and only to point at this
  round and move discharged clauses from "Realization and integration" to a stated
  status.
- It does not open new priority items except within its own scope, named in the
  report with PROMPT.md as authorization.
- Naming ships provisional. Use existing names where they exist; grep before
  introducing one.

============================================================
6. DELIVERABLES
============================================================

projects/deference/rounds/2026-09-09-evaluation-ecosystem-realization/
  README.md                what this round is, in a paragraph
  ECOSYSTEM.md             the model: parties, log, protocol instance, β, R, P, D,
                           principal and advisor policies, market side (§2 above)
  CLAUSE_LEDGER.md         the seven clauses, each DISCHARGED or RESIDUAL, with witness
                           paths and the single assumption each discharge rests on
  END_TO_END.md            one worked trace from issuance to `R_auth`, every symbol
                           computed, every clause evaluated, the bound instantiated
  SETTLEMENT_CHANNEL.md    §4
  COUNTERMODELS.md         every countermodel named above, as exact fixtures
  FOR_HUMANS.md            one page
  PROVENANCE.md, REPORT.md
  src/                     the executable model (stdlib-only, exact rationals)
  tests/                   run under python3 tests/run.py

lean/Workspace/Deference/Contrib/<NewModule>.lean and/or
lean/Workspace/Normativity/Contrib/<NewModule>.lean — the concrete instances, sorry-free,
auditing to the allowed axioms, with nonvacuity witnesses; each file's docstring says
which clause of item 87 it is evidence for.

PRIORITIES.md item 87: update its status line only; do not rewrite the bill.
DECISIONS.md: agent-decided reversible entries for every modelling choice that could
have gone another way (log shape, prohibited class, principal policy class),
appended beneath the last same-dated entry. Nothing here is a maintainer ruling.

REPORT.md must contain: what was built; the clause ledger in summary; the scored
pre-registered expectations of §3 (right and wrong); what deviated from this prompt
and why; what is reserved to the maintainer with its "turns on" line; a "Consumers"
paragraph (§0); and the attribution block per AGENTS.md (prompt author: maintainer,
relayed verbatim; executor model named; date).

Acceptance: python3 tests/run.py green; lake build clean; axiom audit clean; every
cited path resolves; name lint passes. The verdict line of the report states whether
the realization is FULL, PARTIAL-WITH-EXACT-RESIDUALS, or OBSTRUCTED, and a
PARTIAL verdict is the honest default.
