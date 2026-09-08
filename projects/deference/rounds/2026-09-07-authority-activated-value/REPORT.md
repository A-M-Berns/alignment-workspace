# Report

## Verdict

**AUTHORITY-ACTIVATED-VALUE-SURVIVES.**  The legitimacy→deference interface is an
anchored evaluation occurrence whose actual future answer activates ordinary value
securities iff its account is a single authenticated answer with an occurrence-local
legitimate lineage.  Every ingredient is expressible on the existing account calculus;
ordinary LI Value runs on the activated family unchanged; the one new theorem is the
availability transfer at the sharp constant `ε + η`.  The two things the construction
does not supply — that evaluations happen, and that a process-certified answer is the
principal's — are typed as external and filed.

## The theorem stack

| # | statement | label | where |
|---|---|---|---|
| 1 | `activated T := (T.fates = {answered})`; answer activates, closed and live do not, any second leaf deactivates | LEAN | `AuthorityActivation.lean` §1 |
| 2 | the first answer binds: a terminal account is fixed under every step; activation persists | LEAN | §2 |
| 3 | propagation is occurrence-local: `o`'s propagated account depends only on `o`'s source account and the certificate | LEAN | §3 |
| 4 | occurrence-local legitimacy `LegitimateForSegment Γ'` is a projection of `LegitimateSegment` with the same evolution; composes; carries conservation | LEAN | §4 |
| 5 | payload-blind certification: `(∃ρ, Cert ρ V) ↔ ∃π, ProcessCert π` | LEAN | §5 |
| 6 | pairwise difference and conditional-argmax identity under common activation | LEAN | `ActivatedValue.lean` |
| 7 | availability transfer `regret_V ≤ ε + D·η`, sharp at `D = 1`, for any followed strategy; asymptotic form | LEAN | same |
| 8 | per-action certification keeps the transfer at `ε + max_a η_a` and breaks the argmax identity | LEAN | same |
| 9 | Value on `{U_{n,a}}` is the inherited `value_asymptotic` with activated LUVs, hypotheses unchanged | PAPER | `LI_DEFERENCE_COMPOSITION.md` §2 |
| 10 | the no-preview receipt is the admissible-domain condition of Value | FIX + reading | §3 there |
| 11 | availability `𝔼ⁿ[C_n] → 1` from `lic_provind_true` when every `C_n` settles true | PAPER | §6 there |
| 12 | semantic authentication of receipts; P-authorship; that the ecosystem answers | EXT | `AUTHORITY_ACTIVATED_VALUE.md` §§4, 7 |
| 13 | fixtures A–I plus the witness-menu constant and the transfer sweep | FIX | `COUNTERMODELS.md` |

## Existing versus new

Existing and reused without change: `Occ`, `Req`, `anchor`, `Protocol.AnswerOK`,
`AnswerReceipt.event`, `Authority`, `LocalLaw`, `Program`, the three fates, `Step`,
`Segment`, `Evolution`, `Conservation`, `OpennessSemantics`, `RobustOpenActual`,
`value_asymptotic`, `value_iff_totalTrust`, `LUV`, `expectApprox`, `lic_provind_true`.

New definitions: `Program.activated` (one line on existing data); `OpenAtFor`,
`LegitimateForSegment` (the projection); `Neutral` (a two-field abstraction for the
factorization statement); the `ActivatedValue` algebra.

New primitives: **none**.  No `ContinuationWarrant`, no `AuthorityLineage`, no
payload-bearing receipt, no new legitimacy conjunct.

## What failed under adversarial pressure

- **The hard-selector form of the target inequality** as written in the prompt
  (`â_n ∈ argmax_a 𝔸ⁿ(U_{n,a})`) is available only on the admissible domain; the
  self-referential fixture **I** has no consistent hard selection.  The construction
  survives because the no-preview receipt puts the menu on the domain, and the soft
  form of the ported theorem is what is on `main` anyway.
- **Global legitimacy as the consumer hypothesis** fails on fixture **H**: an
  unrelated routeless concern voids the evaluation.  Replaced by the projection.
- **"Resolved" as the activation condition** fails on fixture **E**: a closure has no
  payload, and any default makes the agent defer to itself.
- **Per-action certification** fails the argmax identity (fixture **D**), though not
  the transfer bound.
- **An unactivated constant in the witness menu** reopens the certifiability channel;
  the constant must be activated too.
- **The constant `2`** in `ε + 2η` is not needed; `ε + η` is exact.

## Dependencies

Takes as hypotheses `2026-09-08-canonicalization` (the accounted-state and
legitimate-segment spine), `2026-09-06-mathematical-consolidation`
(`OccurrenceIntegrity`), `2026-09-05-noncapture-certificate` (`RobustOpenActual`),
`2026-08-12-corpus-reconciliation` (the Value/Total Trust record and the punishing
menu), and `2026-08-11-faithful-acceleration` (`InheritedAlgebra.lean`).  Cites
`2026-09-06-incentive-nonpreemption` for the PR #90 composition remark only.

## Deviations and prompt corrections

- The prompt writes `H_n` both for the novice's expectation and for the history
  prefix; the round uses `𝔼ⁿ` and `h_m`.
- The prompt's `EvalReq(P, α, Q, sessionId)` is kept with `P` read as a *role
  identity* `ρ_P`, since the holder may change by authorized succession while the
  anchor may not; and an output type `τ` is added to the anchor because the value
  vector's interpretation must be fixed at issuance.
- The prompt's `C_n` combines the answer with "the relevant legitimate segment"; the
  round makes the segment occurrence-local (`Γ_n`), which the prompt asked to
  investigate and which fixture **H** forces.
- The prompt asks for a "generic common-activation regret lemma" and a "sharp
  availability transfer inequality"; these are one theorem family here, stated for a
  fixed selection, for a followed strategy, and asymptotically.
- The threshold-security reconstruction is checked as a fixture and by the pinned
  LUV definition, not proved in Lean: it is the dependency's own grid error.
- Wiki edits: one sentence each on `Openness-Coverage-and-Non-Capture.md` and
  `Legitimacy.md` recording that Robust Openness is the access half of non-capture
  and that authorship is a separate external contract; one paragraph on
  `Deference.md` pointing at this round.  Nothing renamed.
- The exact claim "this future judgment is genuinely P-authored" is labelled EXT
  throughout and never derived.

## What this does not establish

- That any ecosystem produces certified answers, or at what rate (`η_n`); that any
  protocol's receipts mean what they say; that `ProcessCert = 1` makes `V` the
  principal's own.
- The tower `Mart_{H→A}` on activated LUVs; it is the inherited theorem's deference
  hypothesis.
- An `RpnThresholdCodeSeq` witness for the activated menu in a concrete arithmetic
  instantiation.
- Anything about menus whose candidate set changes, multi-parent laws, or contested
  succession of the principal role.
- Full incentive corrigibility; the PR #90 remark supplies an object for item 84,
  not the bridge.

## Corrections applied by the consolidation round

Recorded here so the round's original claims are legible against the repair
(`../2026-09-08-legitimate-deference-consolidation/MAIN_READINESS.md`):

- **`AnswerOK` placement.**  §3 of `AUTHORITY_ACTIVATED_VALUE.md` put `Bind(V)` inside
  `AnswerOK`; the field is evaluated at the strict prefix and takes no event.  Repaired
  to a derived predicate over the receipt's `event` and the history's payload.
- **Total `V`.**  The evaluation is a partial object on certified worlds; the total `V`
  survives as a completion, and activated securities are completion-invariant.
- **"Occurrence-local legitimacy".**  `LegitimateForSegment` is scope-local openness
  over global Integrity; the occurrence-local object is `LocalLegit`.
- **No-preview as the scope condition.**  The scope condition is selection-induced
  channel blindness `Blind R P_sel`; no-preview is one implementation and is
  insufficient alone (leakage).
- The verdict line's "no-preview receipt" clause is amended accordingly in `README.md`
  and `state/rounds.json`.

## Outstanding maintainer actions

1. None reserved.  Two decisions are adopted agent-decided in `DECISIONS.md`
   (2026-09-07): the activation semantics and the occurrence-local consumer
   hypothesis.  `PRIORITIES.md` item 87 files the residual bridge.
2. Whether to register the Lean declarations against item 87 once a realization
   discharges it; nothing is registered now.

## Attribution

- Prompt author: maintainer, relayed verbatim.
- Executor: Claude Fable 5.1 (Anthropic).
- Date: 2026-09-07.
