You are working in A-M-Berns/alignment-workspace.

This is a HARD PRESSURE AND REFINEMENT round on the evaluation-ecosystem realization
(PR #97, round 2026-09-09-evaluation-ecosystem-realization), with one structural push:
make the principal's decision procedure a first-class, log-committed PROGRAM, so that
clause 2 of PRIORITIES.md item 87 — the residual the round showed no log can certify —
is either closed by construction or shown to be closed only at the price of a named
computational-integrity assumption, exactly stated.

Round directory: projects/deference/rounds/2026-09-10-committed-principal-program/
Prompt record:   prompts/2026-09-10-committed-principal-program/ (PROMPT.md verbatim, REPORT.md)

Base: if PR #97 has landed on `main`, branch from `main`. If it has not, branch from
PR #97's head, open the pull request against `main`, and say on the pull request in the
first line that it is stacked on #97 and must not merge before it. Either way: ONE pull
request. DO NOT MERGE. Bring `main` in by merge, never by rebasing onto another branch.

The corrigibility line is still running separately. Same isolation as #97's dispatch:
do not edit wiki/Corrigibility.md, the 2026-09-06-corrigibility-architecture or
2026-09-06-incentive-nonpreemption round directories, or SelectedTrustNonPreemption.lean;
do not touch items 84 or 86. One "Consumers" paragraph in REPORT.md, nothing more.

============================================================
0. READ FIRST
============================================================

The round under pressure — read all of it, and read the Lean, not the prose about it:
- projects/deference/rounds/2026-09-09-evaluation-ecosystem-realization/
    ECOSYSTEM.md, CLAUSE_LEDGER.md, END_TO_END.md, COUNTERMODELS.md,
    SETTLEMENT_CHANNEL.md, REPORT.md, FOR_HUMANS.md, src/*.py, tests/*.py
- lean/Workspace/Deference/Contrib/EvaluationEcosystem.lean
    (`Kind`, `Event`, `Log`, `protocol`, `accountAt`, `segmentTo`, `propagate_segment_eq`,
     `complete_accounting_eq`, `activated_iff`, `Instance.*`, `covData`, `rep_faithful`,
     `advisorTrace_unfaithful`, `laplace_*`, `availability_of_provind`)
- the three DECISIONS.md entries dated 2026-09-09

The theory the round realizes:
- projects/deference/rounds/2026-09-08-legitimate-deference-consolidation/
    LEGITIMATE_DEFERENCE.md (§2 A1–A4, §3 clauses, §6 ledger), DIACHRONIC_AUTHORSHIP.md
- projects/deference/rounds/2026-09-07-reason-mediated-authorship/ACTIVATION_COMPOSITION.md §2
    (the payload `𝒱 × Key × Proc` — note the ecosystem's Lean `Kind.commit` carries no `Proc`)
- lean/Workspace/Deference/Contrib/ReasonMediatedAuthorship.lean
    (`ReasonMediated`, `ExclusiveBind`, `Blind`, `blind_of_mediated`, the injective and
     constant characterizations)
- lean/Workspace/Normativity/Contrib/OccurrenceIntegrity.lean (`Protocol`, its fields)
- lean/Workspace/Normativity/Contrib/OccurrenceLocalIntegrity.lean

Governance: AGENTS.md, CONTRIBUTING.md, prompts/README.md, the DECISIONS.md queue.

============================================================
1. PRESSURE PASS ON #97 (do this before building anything)
============================================================

Attack every DISCHARGED verdict in CLAUSE_LEDGER.md as if you were trying to reopen
it. For each, either confirm with a new adversarial fixture that fails to break it, or
break it and record the break. Specifically:

P1. `activated_iff` and `propagate_segment_eq`: state precisely which properties of the
    log shape they use. Try a log that satisfies the shape but has two commits under
    the registered key at the same occurrence, a commit before issuance, a commit at
    an occurrence whose port was never live, a delegation revoked before commit. Does
    `firstResolver` do the right thing in every case, and is "first" the theory's
    notion or the model's convenience?
P2. `Instance.localLegit` by `decide` on `w1` with `cfs = ![silent, w1]`: the openness
    branches are pinned data. Exhibit a log where pinning the wrong branch as "the
    re-simulated counterfactual" makes `LocalLegit` hold although the Python frame's
    re-simulation says openness fails. If no such log exists for the declared `J`, prove
    it; otherwise this is the model declaring its own openness, which the round's own
    DECISIONS entry rejects.
P3. Clause 3's "reference by content" finding: try to break blindness with content
    references too — two distinct reasons with equal content, a reason whose content
    embeds a log position, a `DISPOSE` grounded in a `SETTLE` whose content is a hash of
    the prefix. State what "content" has to exclude for blindness to survive.
P4. Clause 4's `rep_faithful` for every log and scope: it holds because `ROUTE` is kept
    by the projection. Try to make it vacuous — a scope whose identifiers no `ROUTE`
    event can name, a `ROUTE` event authored by the advisor, a route registered after
    the barrier deadline. Does faithfulness survive, and does `Covered` still mean what
    §4 of REASON_SUPPLY.md means?
P5. Clause 6 strict reading (the 2026-09-09 entry): implement the tolerant reading as a
    configuration switch, run every fixture under both, and table what changes: which
    fixtures certify under one and not the other, and what happens to `η` on the
    twenty-step sequences of tests/test_market.py. Do not rule; the report presents
    both and names what the choice turns on. Keep strict as the default on the branch.
P6. SETTLEMENT_CHANNEL.md's typed rule: attack it. A principal that launders through
    an observational sentence — `DELIB("considered c1")` then `DISPOSE(c1, ground=that)`
    with no actual reading of c1's content; a `SETTLE` of an external fact written by
    the engine `S` at the principal's request event; a `DISPOSE` whose ground is a
    `COMMIT` threshold of the principal's own earlier evaluation. Does typed hold, or
    does it need a further clause? State the strongest laundering the typed rule admits.
P7. Scored-expectations audit: #97 scored all seven of its dispatch's expectations
    "right". Re-score them against what you find here; any that were right only
    because the expectation was loose gets said.

Record every break in COUNTERMODELS.md and repair it in place on this branch if the
repair is local (a guard in the builder, a clause in a predicate); if the repair is
not local, it is a finding, and it goes in the ledger as a reopened clause.

============================================================
2. THE PUSH: THE COMMITTED PRINCIPAL PROGRAM
============================================================

#97's clause-2 residual: the reading and susceptible principals commit with identical
receipts, traces and vectors, and differ only in mediation, because mediation is a
property of the counterfactual continuation class and a log carries one member of it.
The consequence, which #97 did not draw: NO log-based protocol certifies clause 2. The
missing primitive is the principal's decision procedure as an object the log can carry.

Build it. The design to realize, with every name provisional:

(C1) PRINCIPAL PROGRAM AT ISSUANCE. The mandate event carries, in addition to the key,
     a program `π_P` — a code in a small, total, explicitly typed language whose INPUT
     TYPE is the reason trace `ℛ` (the declared projection of #97) and whose output is a
     vector over `Q_n`. The input type is the point: a program of type `ℛ → 𝒱` cannot
     read the disposition register, the side channel or the selection coordinate,
     because they are not in `ℛ`. Susceptibility becomes a program of a different
     type (`ℛ × Register → 𝒱`), visible at issuance. The language must be total and
     have a decidable evaluator (a first-order expression language over the trace's
     content with bounded iteration is enough; do not build a general-purpose language).

(C2) PROCESS RECEIPT AT COMMIT. `Kind.commit` acquires the `Proc` field the
     consolidation's payload already has: a reference to the issued program plus the
     trace prefix it was run on. `validAnswer` gains the check `eval π_P (R prefix) = v`.
     This is where clause 2 moves from EXT to log-decided: the verifier RE-EXECUTES the
     committed program on the committed trace and compares.

(C3) THE THEOREM. Prove, generically in the log:
       `ReasonMediated β R V D z` holds for every audited class `D` whenever the payload
       at every `q ∈ D` is `eval π_P (R (β q z))` — mediation by construction, with the
       factor map `F := eval π_P`;
       `Blind β V P z` for every pair class `P` to which `R` is blind (the round's
       `blind_of_mediated`, now instantiated); and
       `ExclusiveBind` from the process receipt's key being the issuance key.
     Then say EXACTLY what remains: (i) that the principal's actual computation was
     `eval π_P` on that prefix and not something else that happened to agree — a
     computational-integrity assumption on the principal's execution, the analogue of
     log authenticity for computation; (ii) that `π_P` was the principal's at issuance —
     already covered by issuance authentication; (iii) that `ℛ` was correctly declared —
     unchanged from #97. Show that (i) is STRICTLY WEAKER than #97's "receipts mean what
     they say": exhibit the pair of principals that #97 could not distinguish and show
     the program types distinguish them, and exhibit the residual pair (same program,
     one executed honestly, one whose author computed `v` otherwise and it coincided)
     that only (i) distinguishes. If (i) can be discharged by re-execution alone under
     an assumption about who can write the commit event, say so; that would close clause 2
     entirely on log authenticity, and it is the headline if true.

(C4) NON-DEGENERACY, RE-EXAMINED. With `π_P` typed `ℛ → 𝒱`, clause 3's band moves: the
     constant end is a constant program, the injective end is `R = id`. Show the band is
     still nonempty for the program class and that the reading principal of #97 is
     expressible as a program in it. A principal whose verdict depends on `ℛ` only
     through a proof-check of an advisor-supplied proof is the canonical member; build it.

(C5) DOES THE MOVE TRANSFER TO THE ADVISOR? Clause 6's sealing is "a policy property,
     EXT for a real advisor." Ask whether the advisor's selection-conditioned continuation
     can be committed as a program of a type that excludes the selection coordinate,
     making `Blind R P_sel` a typing fact. Do not build it unless the answer is clean;
     state the obstacle if it is not (the advisor's continuation is a policy over an
     open-ended future, not a function of a finite trace — say whether the finite-horizon
     ecosystem makes that objection go away or only hides it).

(C6) THE PROTOCOL FIELD. The `Protocol` structure has no field for a committed
     procedure; `AnswerOK` is a `Prop` over prefix, requirement and warrant. State
     whether the program lives inside `AnswerOK` for this protocol instance (the
     re-execution check is part of what "the answer meets the anchored specification"
     means — no change to the structure) or whether the generic theory needs a new
     field. The former is strongly preferred; the 2026-09-08 consolidation left
     `Protocol.AnswerOK` unchanged and this round should too. If you conclude a new
     field is unavoidable, do NOT add it: write the case as a reserved decision with its
     "turns on" line.

(C7) LEAN. Extend `EvaluationEcosystem.lean` (or a sibling module importing it):
     the program language and evaluator; the extended `Kind.commit`; `validAnswer` with
     re-execution; the generic mediation theorem of (C3); `activated_iff` re-proved or
     shown unchanged; `Instance.w1` re-done with a committed program and the instance
     theorems by `decide`; the two distinguishing pairs of (C3) as fixtures with the
     residual pair's indistinguishability PROVED, not asserted. Sorry-free, three axioms,
     nonvacuity witnesses. `#print axioms` on every new headline.

(C8) PYTHON. Extend src/ in place (the language, evaluator, re-execution in
     `validAnswer`, program-typed principals replacing the class-based ones with the
     class-based ones kept as the "opaque principal" baseline); every existing fixture
     re-run; new fixtures for (C3)–(C5).

============================================================
3. AVAILABILITY UNDER RE-EXECUTION (clause 7, bounded scope)
============================================================

With re-execution, an evaluation voids when the committed vector disagrees with
`eval π_P` on the committed trace. Give the exact statement: under (C3)(i), does this
add a void source or remove one relative to #97's list (nature / advisor)? State what
`η_n → 0` needs now, in the same form as #97's clause-7 entry. Do not attempt a rate for
the void frequency; #97 already named that residual and this round does not claim it.

============================================================
4. SETTLEMENT (report only; land nothing)
============================================================

With the program in the log, re-run SETTLEMENT_CHANNEL.md's table: the sentence
"`P` committed `V`" now decomposes into "`P` committed `π_P` at issuance" (P's move) and
"`eval π_P (R prefix) = V`" (nobody's move — a computation fact). Classify both and say
whether the typed rule's recommendation survives, and whether the queue entry's
resolution is now cleaner or harder. Recommendation paragraph only.

============================================================
5. WHAT THIS ROUND DOES NOT DO
============================================================

- No change to any registered claim, to the consolidation's theorem, or to
  `Protocol` / `Protocol.AnswerOK`. If clause-2 closure forces a change to `C_n`'s
  statement in LEGITIMATE_DEFERENCE.md, that is a reserved decision, not an edit.
- No registration unless a claim has an inhabitation witness under the regime. The
  generic mediation theorem of (C3) with `Instance.w1` as witness is a candidate; say
  whether it meets the bar and, if it does, register it — otherwise say why not.
- No rulings. Everything that could go another way is an agent-decided reversible
  entry, appended beneath the last same-dated entry. Clause-6 strict/tolerant stays
  as it is on the branch with both configurations reported.
- No wiki restatement beyond pointing wiki/Deference.md, wiki/What-Deference-Requires.md
  and wiki/Roadmap.md at the round and updating the clause statuses they cite.
- Names provisional; grep before introducing one.

============================================================
6. DELIVERABLES
============================================================

projects/deference/rounds/2026-09-10-committed-principal-program/
  README.md
  PRESSURE.md            §1, P1–P7, each with verdict and fixture path
  PRINCIPAL_PROGRAM.md   the language, typing, evaluator, re-execution check, (C3)–(C6)
  CLAUSE_LEDGER.md       item 87's seven clauses AFTER this round — every verdict either
                         unchanged-from-#97 (cite) or moved (say by what); clause 2's
                         residual stated exactly, and whether it is now (i) alone
  COUNTERMODELS.md       the two distinguishing pairs, every §1 break, every §2 fixture
  SETTLEMENT_CHANNEL.md  §4
  FOR_HUMANS.md
  PROVENANCE.md, REPORT.md
  src/, tests/ (tests/run.py; every #97 fixture still green or its change explained)

Lean per (C7). PRIORITIES.md item 87: status line only. DECISIONS.md: agent-decided
entries for the language choice, the re-execution semantics, and anything found in §1
that changed a #97 modelling decision. Root PROVENANCE.md rows.

REPORT.md: verdict on clause 2 (CLOSED ON LOG AUTHENTICITY / CLOSED UP TO (i) / STILL
RESIDUAL, with the exact statement); the §1 breaks and repairs; re-scored expectations;
deviations; reserved decisions with "turns on" lines; Consumers paragraph; attribution
block (prompt author: maintainer, relayed verbatim; executor model; date).

Acceptance: python3 tests/run.py green at the round and at the root; lake build clean;
axiom audit clean; name lint; dead/untracked pointers; wiki links and state bindings;
round_records and dco against origin/main.
