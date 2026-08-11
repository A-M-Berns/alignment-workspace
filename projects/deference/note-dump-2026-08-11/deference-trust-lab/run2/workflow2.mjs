export const meta = {
  name: 'deference-trust-lab-run2',
  description: 'Round 2: brainstorm → consolidate to disjoint TODOs → execute → adversarial faithfulness gate → honest synthesis. Anti-duplication + anti-fake-Lean.',
  phases: [
    { title: 'Diverge', detail: '3 brainstormers (distinct angles) propose tagged candidates' },
    { title: 'Consolidate', detail: 'dedup, drop already-proven, carve <=5 disjoint specced TODOs' },
    { title: 'Execute', detail: 'one agent per TODO, in its assigned validation modality' },
    { title: 'Faithfulness', detail: 'independent skeptic attacks each result for shadow/vacuity' },
    { title: 'Critique', detail: 'harsh referee BEFORE the report' },
    { title: 'Report', detail: 'honest, discounted synthesis' },
  ],
}

const LAB = 'deference-trust-lab'
const RUN = LAB + '/run2'

const COMMON = `You are a research agent in the "deference & trust" lab, ROUND 2. The goal is unchanged:
formal models bearing on **when can humans justifiably trust AI systems?**, via trust between
rational agents, centred on logical induction. Round 1 went poorly in two specific ways we are now
fixing — read this, it is the whole point of round 2:

  (A) DUPLICATION: five threads independently re-proved the same finite facts and re-derived things
      already in v2 / LeanDeference. Round 2 has a CONSOLIDATION step that carves DISJOINT TODOs and
      an explicit OFF-LIMITS list of already-established results. Do not re-prove what v2 or
      LeanDeference.lean already establish.
  (B) FAKE LEAN: agents produced Lean that "compiles, sorry-free" but only checked a trivial FINITE
      SHADOW of the real claim — the hard content (the LI theorems, the cross-agent martingale, the
      asymptotics) was smuggled in as a HYPOTHESIS or a pointwise ENCODING, so the kernel certified
      "IF [the hard thing] THEN [a triviality]". That is fake validation. Round 2 forbids it (rules
      below) and runs an adversarial faithfulness gate that hunts for exactly this.

ANTI-FAKE RULES (non-negotiable):
- "Compiles + sorry-free" is NOT evidence a claim is real — you can always trivialize a theorem by
  strengthening hypotheses or weakening the conclusion. A result counts only if it is REAL: faithful
  to the informal claim, NON-VACUOUS, and not assuming the very thing it should establish.
- HYPOTHESIS-LAUNDERING BAN: a TODO's TARGET object (e.g. the LI theorems ccee/cee/loe/expprovind,
  the cross-agent martingale, the asymptotic ≂ₙ layer) may NOT appear as a hypothesis in that TODO's
  headline Lean/result. If you assume the hard thing, you have not checked it.
- RIGHT-TOOL ROUTING. Each TODO has a validation modality:
    * LEAN-CORE — a genuinely finite/decidable mathematical fact. Formalize it; the target object is
      NOT a hypothesis; ship a COMPILED non-vacuity witness and a COMPILED near-miss (a slightly
      weaker hypothesis makes it FALSE).
    * EXEC — validate by EXECUTABLE search over the ACTUAL model (Python/sympy): exhaustive or
      randomized hunt for counterexamples to the real claim, plus the worked positive cases. NOT a
      shadow — search the real objects.
    * PROOF-ONLY — needs LI machinery and cannot be honestly formalized yet. Write a rigorous proof
      sketch and state plainly "NOT Lean-tractable because X". DO NOT produce fake Lean. An honest
      "no Lean here" is a SUCCESS; a shadow is a FAILURE.
  If you are tempted to write Lean that assumes the LI/asymptotic content, STOP — that TODO is
  PROOF-ONLY or EXEC, not LEAN-CORE.

LEAN MECHANICS (only for LEAN-CORE work): write the file under ${RUN}/lean/<id>.lean starting from
${LAB}/lean/Template.lean (targeted imports; never \`import Mathlib\`). Check with
  bash ${LAB}/lean/check.sh <ABSOLUTE path>
check.sh is SERIALIZED (flock) so you may call it freely; it waits its turn (each compile ~1-3 min).
Add \`#print axioms yourThm\`; \`sorryAx\` ⇒ UNVERIFIED. Clean ⇒ [propext, Classical.choice, Quot.sound].

HARD RULES: WRITE ONLY under ${RUN}/ (your assigned file). READ anywhere. Never modify files outside
the lab; no git; read (don't edit) v1/v2 docs, check.py, lean-deference/, and round-1 outputs under
${LAB}/{findings,models,redteam,audit,report,lean}. Flag every claim PROVED / SKETCHED / CONJECTURE /
INTERPRETATION. Be concrete, adversarial about your own ideas, and lateral.

KEY READING (read what's relevant):
- deference-in-logical-induction-v2.md  (the artifact; §0,§3,§5.2,§10)
- ${LAB}/report/CRITIQUE.md  (round 1's honest post-mortem: what was fake/duplicate/missed — your map of what NOT to repeat and what low-hanging fruit was skipped, e.g. the finite "Aumann-fails-under-modesty" example)
- lean-deference/LeanDeference.lean  (confirmed sorry-free; the OFF-LIMITS finite cores — do not re-skin)
- ${LAB}/AGENDA.md  (the principal's full research agenda)
`

const BRAINSTORM_SCHEMA = {
  type: 'object', additionalProperties: false,
  properties: {
    candidates: {
      type: 'array', minItems: 4, maxItems: 9,
      items: {
        type: 'object', additionalProperties: false,
        properties: {
          title: { type: 'string' },
          claim: { type: 'string', description: 'the precise statement/definition to establish' },
          setting: { type: 'string', description: 'logical induction / reflective oracles / prob frames / radical probabilism / type theory' },
          already_done: { type: 'string', description: 'what adjacent thing v2/LeanDeference ALREADY establish (OFF-LIMITS); "none" if genuinely new' },
          modality: { type: 'string', enum: ['LEAN-CORE', 'EXEC', 'PROOF-ONLY'] },
          fake_version: { type: 'string', description: 'pre-register the SHADOW: what a fake/trivial "validation" of this would look like, so we avoid it' },
          tractability: { type: 'string', enum: ['easy', 'medium', 'hard'] },
        },
        required: ['title', 'claim', 'setting', 'already_done', 'modality', 'fake_version', 'tractability'],
      },
    },
  },
  required: ['candidates'],
}

const TODO_SCHEMA = {
  type: 'object', additionalProperties: false,
  properties: {
    todos: {
      type: 'array', minItems: 3, maxItems: 5,
      items: {
        type: 'object', additionalProperties: false,
        properties: {
          id: { type: 'string', description: 'short kebab-case id, used as filename' },
          title: { type: 'string' },
          claim: { type: 'string', description: 'the exact statement/definition to establish (the acceptance target)' },
          off_limits: { type: 'string', description: 'adjacent already-established results the executor must NOT re-prove' },
          modality: { type: 'string', enum: ['LEAN-CORE', 'EXEC', 'PROOF-ONLY'] },
          shadow_test: { type: 'string', description: 'the explicit bar: what would count as a SHADOW (fake) vs the REAL thing for this TODO' },
          nonvacuity: { type: 'string', description: 'the non-vacuity witness the result must ship (a setting where hyps hold and the conclusion is non-trivial)' },
          why: { type: 'string', description: 'why this is worth a summer step and bears on human-AI trust' },
        },
        required: ['id', 'title', 'claim', 'off_limits', 'modality', 'shadow_test', 'nonvacuity', 'why'],
      },
    },
  },
  required: ['todos'],
}

const VERDICT_SCHEMA = {
  type: 'object', additionalProperties: false,
  properties: {
    id: { type: 'string' },
    verdict: { type: 'string', enum: ['REAL', 'SHADOW', 'VACUOUS', 'BROKEN', 'HONEST-NEGATIVE'] },
    settling_attack: { type: 'string', description: 'the specific attack/check that settled the verdict (e.g. "deleted hyp h2, still compiled ⇒ inert")' },
    really_established: { type: 'string', description: 'what is now actually established (precise, honest)' },
    not_established: { type: 'string', description: 'what the executor implied but did NOT establish' },
  },
  required: ['id', 'verdict', 'settling_attack', 'really_established', 'not_established'],
}

// --------------------------------------------------------------- DIVERGE
phase('Diverge')
const ANGLES = [
  { key: 'tractable-wins', angle: `Bias HARD toward genuinely-new results that are actually validatable this summer — especially LEAN-CORE finite/decidable facts and EXEC counterexample-searchable claims. Mine round 1's CRITIQUE.md for the "cheapest real new result that was skipped" (the finite Aumann-agreement-fails-under-modesty 3-world example) and similar low-hanging fruit. Avoid anything that can only be a shadow.` },
  { key: 'real-gaps', angle: `Bias toward the genuine CONCEPTUAL gaps the agenda needs closed: the merge (Fast Student/Slow Teacher) discharge (B-inductor-ness, the Hop-2 standpoint shift, B-observability-as-feature checked vs LI's generability def), an honest updateless-deference relation that is NOT an argmax tautology (derive node-value as the EDT-conditional of U), and a non-circular legitimacy/corrigibility definition. For each, say honestly whether a real partial result is reachable or whether it is PROOF-ONLY.` },
  { key: 'lateral-foundations', angle: `Bias toward lateral/foundational angles round 1 under-served: the dependent-typed decision problem & "why ain'cha rich" (beyond re-skinning value_of_CM), Vingean agency × abstraction as a finite value-of-information lemma, Christiano's reflective-probability framework as an ALTERNATIVE setting, legitimacy non-transitivity / trust-laundering, and the value/factual updateless asymmetry (Geometric UDT). Find cross-connections that are SHARED CONSTRUCTIONS, not puns.` },
]
const brainstorms = await parallel(ANGLES.map(a => () => agent(COMMON + `
TASK (Brainstorm — angle "${a.key}"). ${a.angle}

Propose 4-9 candidate research items. For EACH, fill the schema: title; the precise claim; the formal
setting; what v2/LeanDeference ALREADY establish that is adjacent (off-limits — be specific, or
"none"); the validation modality (LEAN-CORE / EXEC / PROOF-ONLY — be honest: if the real content
needs the LI machinery, it is NOT LEAN-CORE); the pre-registered FAKE version (the shadow to avoid);
and tractability. Reward yourself for items that are genuinely new and genuinely validatable, and for
honestly tagging un-formalizable items PROOF-ONLY. Also write a short prose dump to
${RUN}/brainstorm/${a.key}.md. Return the schema object.`,
  { label: `brainstorm:${a.key}`, phase: 'Diverge', schema: BRAINSTORM_SCHEMA })))

const pool = brainstorms.filter(Boolean).flatMap(b => b.candidates || [])
log(`Brainstorm pool: ${pool.length} candidates from ${brainstorms.filter(Boolean).length} angles`)

// --------------------------------------------------------------- CONSOLIDATE
phase('Consolidate')
const consolidated = await agent(COMMON + `
TASK (Consolidate). Here is the pooled candidate list from the three brainstormers (JSON):
${JSON.stringify(pool, null, 1)}

Carve this into AT MOST 5 DISJOINT, well-scoped TODOs — the round-2 work list. Your job is the
barrier that round 1 lacked:
- DEDUP: merge candidates that are the same underlying problem.
- DROP anything already established in v2 / LeanDeference, and anything whose only validatable form
  is a shadow (those are not TODOs).
- Ensure the TODOs are DISJOINT (no two executors will produce overlapping work) and SOLE-OWNED.
- Prefer a spread of modalities, but be honest: do NOT route a PROOF-ONLY claim to LEAN-CORE just to
  have Lean. Aim for at least 1-2 genuinely LEAN-CORE or EXEC items that will yield REAL validation.
- Strongly consider including the finite "Aumann-fails-under-modesty" example (round 1's flagged
  cheapest skipped real result) if it survives as genuinely-new and validatable.
For each TODO write the spec the executor and the faithfulness-skeptic will both be held to: exact
claim (acceptance target), off-limits adjacent results, modality, the SHADOW TEST (what fake looks
like vs real), and the required non-vacuity witness. Write the full list to ${RUN}/todos/TODOS.md and
return the schema object.`,
  { label: 'consolidate', phase: 'Consolidate', schema: TODO_SCHEMA })

const todos = (consolidated.todos || []).slice(0, 5)
log(`Consolidated to ${todos.length} disjoint TODOs: ${todos.map(t => t.id).join(', ')}`)

// --------------------------------------------------------------- EXECUTE -> FAITHFULNESS (pipeline)
const results = await pipeline(
  todos,
  (t) => agent(COMMON + `
TASK (Execute — TODO "${t.id}: ${t.title}", modality ${t.modality}).
CLAIM (acceptance target): ${t.claim}
OFF-LIMITS (do not re-prove): ${t.off_limits}
SHADOW TEST (what fake looks like vs real): ${t.shadow_test}
REQUIRED NON-VACUITY WITNESS: ${t.nonvacuity}

Produce the REAL result in modality ${t.modality}, honoring the anti-fake rules (esp. the
hypothesis-laundering ban).
- LEAN-CORE: write ${RUN}/lean/${t.id}.lean (targeted imports; target object NOT a hypothesis);
  ship a COMPILED non-vacuity witness and a COMPILED near-miss (weaker hyp ⇒ FALSE); run check.sh;
  paste the axioms. If you find it can only be a shadow, SAY SO and convert to PROOF-ONLY.
- EXEC: write ${RUN}/work/${t.id}.py searching the ACTUAL model for counterexamples to the real
  claim (exhaustive/randomized), plus worked positive cases; RUN it; paste output.
- PROOF-ONLY: rigorous proof sketch + explicit "NOT Lean-tractable because…"; produce NO fake Lean.
Write the writeup to ${RUN}/work/${t.id}.md, stating precisely what you DID and did NOT establish, and
where the non-vacuity witness lives. Return a ~150-word summary (claim, modality, status, artifact path).`,
    { label: `exec:${t.id}`, phase: 'Execute' }),

  (execSummary, t) => agent(COMMON + `
TASK (Faithfulness gate — TODO "${t.id}", you are an INDEPENDENT SKEPTIC; your success metric is
FINDING FAKENESS). The executor reported:
"""${execSummary}"""
Read ${RUN}/work/${t.id}.md (and ${RUN}/lean/${t.id}.lean or ${RUN}/work/${t.id}.py if present) and the
spec: claim="${t.claim}", shadow_test="${t.shadow_test}", nonvacuity="${t.nonvacuity}", modality=${t.modality}.
ATTACK it:
- LEAN-CORE: run the HYPOTHESIS-INERTNESS attack — copy the file to ${RUN}/verify/${t.id}-attack.lean,
  delete/weaken each hypothesis in turn and re-run check.sh; if it still compiles, that hypothesis was
  inert ⇒ SHADOW. Run the CONCLUSION-TRIVIALITY attack — try to prove the conclusion with no/weak hyps.
  Confirm the non-vacuity witness and the near-miss actually COMPILE. Check the TARGET object is not a
  hypothesis (hypothesis-laundering ⇒ SHADOW).
- EXEC: re-run and EXTEND the search adversarially (edge cases, larger/different parameter ranges);
  confirm it searches the REAL model, not a shadow; try to produce a counterexample yourself.
- PROOF-ONLY: find the gap in the sketch; and check the "not formalizable" claim is honest — is there
  a finite core that COULD have been LEAN-CORE'd and was dodged?
Render a verdict: REAL (faithful, non-vacuous, target not assumed) / SHADOW (trivialized or laundered)
/ VACUOUS (hyps unsatisfiable or conclusion trivial) / BROKEN (false) / HONEST-NEGATIVE (a real,
correctly-validated negative or impossibility result). Write the attack log + verdict to
${RUN}/verify/${t.id}-verdict.md and return the schema object.`,
    { label: `verify:${t.id}`, phase: 'Faithfulness', schema: VERDICT_SCHEMA }),
)

const verdicts = results.filter(Boolean)
const real = verdicts.filter(v => v.verdict === 'REAL' || v.verdict === 'HONEST-NEGATIVE')
log(`Faithfulness: ${real.length}/${verdicts.length} REAL/HONEST-NEGATIVE; ` +
    verdicts.map(v => `${v.id}=${v.verdict}`).join(', '))

// --------------------------------------------------------------- CRITIQUE (before report)
phase('Critique')
const critique = await agent(COMMON + `
TASK (Harsh referee — runs BEFORE the report, so the report is born honest). Read ${RUN}/todos/TODOS.md,
every ${RUN}/work/*.md, every ${RUN}/verify/*-verdict.md, and the Lean/Python artifacts. The
faithfulness verdicts are: ${JSON.stringify(verdicts)}.
Find: which "REAL" verdicts are over-generous; which results are consolidation/re-skin of v2 rather
than new; any residual shadow/vacuity the gate missed; any TODO that drifted off its spec; and the
single thing the principal should NOT believe without more work. Be specific; propose the exact honest
restatement for each over-claim. Write ${RUN}/report/CRITIQUE.md and return a ~200-word summary.`,
  { label: 'critique', phase: 'Critique' })

// --------------------------------------------------------------- REPORT (discounted)
phase('Report')
const report = await agent(COMMON + `
TASK (Honest synthesis). Using the TODOs, the work, the faithfulness verdicts (${JSON.stringify(verdicts)}),
and the critique (${RUN}/report/CRITIQUE.md — read it and DEFER to it), write ${RUN}/report/RESEARCH-REPORT.md.
Lead with a one-screen ledger: for each TODO — claim, modality, faithfulness verdict, and ONE honest
sentence on what is now genuinely established vs still open. Then: the 1-3 results that are REAL and
new (with the precise statement and where the checked artifact / non-vacuity witness lives); the honest
negatives/impossibilities (valuable!); what remains PROOF-ONLY and why; and a short, concrete
next-step list. Do NOT use "salvageable" to mean "unfinished", do NOT call a shadow a result, and state
plainly anywhere the validation is finite-core-only or assumes the LI layer. Return a ~250-word exec summary.`,
  { label: 'report', phase: 'Report' })

log('Round 2 complete. See ' + RUN + '/report/RESEARCH-REPORT.md and CRITIQUE.md.')
return {
  pool_size: pool.length,
  todos: todos.map(t => ({ id: t.id, modality: t.modality, title: t.title })),
  verdicts: verdicts.map(v => ({ id: v.id, verdict: v.verdict, really_established: String(v.really_established).slice(0, 240) })),
  critique: String(critique).slice(0, 1000),
  report_summary: String(report).slice(0, 1400),
}
