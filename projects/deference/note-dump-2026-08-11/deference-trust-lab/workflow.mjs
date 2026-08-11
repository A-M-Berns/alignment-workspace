export const meta = {
  name: 'deference-trust-lab',
  description: 'Research deference/trust between rational agents (esp. in logical induction); build + machine-check formal models toward "when can humans justifiably trust AI?"',
  phases: [
    { title: 'Orientation', detail: 'map existing results + ripe open questions' },
    { title: 'Ideate', detail: 'per-thread divergent idea generation' },
    { title: 'Deepen', detail: 'build a precise toy model + proof sketch per thread' },
    { title: 'Red-team', detail: 'adversarially stress each model' },
    { title: 'Lean-audit', detail: 'existing LeanDeference.lean vs v2 informal claims (read-only)' },
    { title: 'Lateral', detail: 'Vingean agency/abstraction, decision-problem type, wildcards' },
    { title: 'Lean-verify', detail: 'serially kernel-check candidate Lean (RAM-bound)' },
    { title: 'Synthesis', detail: 'master report + adversarial completeness critique' },
  ],
}

const LAB = 'deference-trust-lab'

const PREAMBLE = `You are a research agent in the "deference & trust" lab. Mission: build FORMAL MATHEMATICAL
models that shed light on **under what conditions humans can justifiably trust AI systems**, by way
of trust between rational agents (an agent and its future self; one logical inductor and another; a
slow trusted reasoner and a fast untrusted one). Focus ESPECIALLY on modeling deference within
logical induction, but the other agenda items matter too.

FIRST, read these (READ-ONLY) to ground yourself; do not re-derive what they already establish:
- ${LAB}/SCOPE.md  (rules)
- ${LAB}/AGENDA.md  (the principal's full "Research Ideas May 2026")
- ${LAB}/findings/00-orientation.md  (a map of existing formal results + open questions — read if present)
- deference-in-logical-induction-v2.md  (our main artifact; esp. §0 notation+theorem statements, §1 S4/diagonal, §3 proof, §5.2 finite collapse, §10 deferring to OTHER experts)
Read others as relevant (DDB, Weatherson, the LI paper §4.8/4.11/4.12, and udt-representation-theorem/ for prior endorsement/UDT work).

HARD RULES:
- WRITE ONLY under ${LAB}/ (your assigned file). READ anywhere. Never modify files outside the lab; no git; don't touch the v1/v2 docs, check.py, or lean-deference/ except to READ.
- Flag every claim as PROVED / SKETCHED / CONJECTURE / INTERPRETATION (match the v2 doc's discipline). Surface counterexamples and failure modes, not just supporting arguments. Be creative and lateral.
- Non-formal reasoning first to get ideas; then tighten to precise statements with explicit hypotheses.

LEAN — IMPORTANT RESOURCE LIMITS (read carefully):
- This machine has only ~7 GB RAM. Every Lean compile loads Mathlib into memory (~1-3 GB). So you MUST NOT run \`check.sh\`, \`lake\`, or \`lean\` yourself — if several agents compiled at once the machine would OOM. A SINGLE dedicated "Lean-verify" agent runs later and checks all candidate Lean files serially.
- The EXISTING lean-deference/LeanDeference.lean is ALREADY confirmed: it builds cleanly and its theorems depend only on the standard axioms [propext, Classical.choice, Quot.sound] — no sorry. Do NOT recompile it; treat that as established.
- If your work yields a small, crisp, plausibly-checkable statement, WRITE it as a candidate Lean file under ${LAB}/lean/<your-key>.lean (start from ${LAB}/lean/Template.lean, which has correct, fast-loading targeted imports — do NOT \`import Mathlib\`, that takes ~10 min). Mark it clearly as **UNCHECKED — for the Lean-verify agent**. Keep it tiny and self-contained.
- For EVERY candidate Lean statement, write in plain English exactly what informal claim it is meant to capture, and reason about whether the Lean ACTUALLY says that: faithful hypotheses (not smuggling the conclusion in), non-vacuous, quantifiers matching. A proof can kernel-check and still not mean what you claim — that gap is the single most important thing to flag.`

// ---------------------------------------------------------------------------
phase('Orientation')
const orientation = await agent(PREAMBLE + `
TASK (Orientation): Produce a precise, compact MAP that the other agents will build on. Read the v2
doc (esp. §0, §3, §5.2, §10), deference-in-logical-induction-check.py, lean-deference/LeanDeference.lean,
and skim DDB + the LI paper's §4.12. Write ${LAB}/findings/00-orientation.md containing:
1. The existing LI-deference result in one tight paragraph: what "Value (LI form)" says, what premise drives it (the conditional martingale / LUV-Total-Trust, thm:ccee 4.12.3), and the §10 modularization (novice's own coherence is free; the cross-agent martingale is the only expert-specific premise).
2. A glossary of the load-bearing formal objects an LI-trust model needs: logical inductor / market / trader, the LI criterion (no efficient trader exploits the market), 𝔼_n, ≂ₙ/≳ₙ, deferral function f, market-generable weights, continuous indicator, Self-Trust (4.12.4), the finite-collapse impossibility (§5.2).
3. What the existing Lean (LeanDeference.lean) actually contains (theorem-by-theorem: name → informal meaning) and what it does NOT cover. (It is confirmed sorry-free with standard axioms.)
4. A ranked list (most-formalizable first) of 8-12 concrete open questions across ALL agenda threads, each phrased as a crisp candidate proposition or definition-to-pin-down, with a one-line note on which formal setting (logical induction / reflective oracles / probability frames / radical probabilism) fits best.
Return a 200-word summary of the map (the file is the full artifact).`,
  { label: 'orientation', phase: 'Orientation' })

// ---------------------------------------------------------------------------
const THREADS = [
  {
    key: 'merging-inductors',
    title: 'Fast Student / Slow Teacher (merging logical inductors)',
    seed: `CENTRAL THREAD. Sam Eisenstat's construction: slow-but-trusted inductor H_t (humans), fast-but-untrusted A_t (AI). Define B_t by asking the AI for its expectation of the FUTURE human: B_t(φ) = 𝔼^A_t(⌜ℙ^H_{f(t)}(φ)⌝). Conjecture: if A has good feedback about H and f grows fast enough, then (i) B_t is itself a logical inductor, and (ii) H_t (weakly) endorses B_t in the LI Self-Trust sense. This is the SAME cross-agent No-Expected-Net-Update structure as v2 §10 — make that bridge explicit. Then: can "good feedback" be obtained from a basin-of-corrigibility bootstrap (AI uses a good-enough model of human-endorsed reasoning to better estimate humans, iterate) instead of assumed? What about an inner-alignment trader that defects after trust is won?`,
    deepenFocus: `Pin down precisely: (a) the LI criterion B_t must satisfy and a proof-sketch that B_t inherits inductor-ness from A (its prices are A's market-generable estimates of H's future prices); (b) the exact statement of "H endorses B" in LI terms and how it reduces to a cross-agent martingale between H and B, citing v2 §10's premise; (c) the smallest toy model (few sentences, explicit f) where you can compute and check the endorsement numerically. Give a worked micro-example.`,
  },
  {
    key: 'weak-endorsement-deference',
    title: 'Weak endorsement ⇒ weak deference; self-reference / Gödel',
    seed: `DDB use the "random-variable trick" (beliefs-about-beliefs as events over a world-set), consistent with full self-knowledge, dodging Gödel. LI's Self-Trust (4.12.4) is the Gödel-ROBUST weakening of Reflection. v2 already shows LI-Total-Trust (LUV form of 4.12.3) ⇒ Value. So the v2 result IS already a "weak-endorsement ⇒ weak-deference" theorem. Make this precise and sharp: weak-reflection (LI 4.12.4) is to Reflection as weak-deference (LI Value, v2 §2) is to Value — state the exact correspondence and what is lost/gained. Then: does the Diagonal Lemma make "perfect alignment" impossible in a precise sense, and what is the right weakening that survives (soft/continuous conditioning, asymptotic)? Connect to Dorst's claim that uncertainty-about-one's-beliefs reshapes common knowledge / Aumann.`,
    deepenFocus: `State a precise theorem schema "weak-endorsement ⇒ weak-deference" in the LI setting and identify exactly which LI theorems discharge it (vs which are assumed). Give the cleanest impossibility statement: a Gödel/Löb sentence that makes hard endorsement+hard deference jointly unsatisfiable, and the soft version that IS satisfiable. If a small algebraic core is plausibly Lean-checkable (e.g. "hard conditioning on the liar gives 0"), write it as a CANDIDATE Lean file (UNCHECKED) for the Lean-verify agent.`,
  },
  {
    key: 'legitimacy-corrigibility',
    title: 'Legitimacy & corrigibility',
    seed: `Endorsement is a property of the TRUSTER (Alice), ~ "Alice thinks Bob's beliefs track reality / Bob's process is truth-tracking." Define LEGITIMACY: a belief-formation process is legitimate-to-H iff H (weakly) endorses its outputs. Wireheading/reward-hacking/manipulation = compromising the legitimacy of the training signal. The drug-avoidance analogy: a rational agent does NOT endorse a future addicted-self's opinions, so it avoids the drug now even knowing it would enjoy it — formalize this as an endorsement/deference FAILURE that is rationally anticipated. CORRIGIBILITY: AI is corrigible where it sees human shutdown/modification as legitimate. Read udt-representation-theorem/ (Meaning&Agency, Complete Feedback, Legitimate Deliberation references) for the principal's prior framing.`,
    deepenFocus: `Give a formal definition of "H endorses process Π" and "Π is legitimate-to-H" in either the probability-frame or LI setting. State a toy theorem: an agent that evaluates futures by its CURRENT endorsement (not its future possibly-manipulated endorsement) declines a manipulation/wirehead that raises future-reported-utility. Then sketch a corrigibility statement: conditions under which the AI defers to a shutdown signal because it endorses the signal-generating process, plus an impossibility/limit (what corrigibility-as-endorsement canNOT buy). Flag where this needs updatelessness.`,
  },
  {
    key: 'updateless-deference',
    title: 'Updatelessness & deference',
    seed: `Endorsement and deference come apart under ACAUSAL consequences: a more-knowledgeable future self might refuse a profitable counterfactual mugging, blow a transparent Newcomb, etc. — so the updateful endorsement⇔deference equivalence breaks. Question: in a more updateless setting, what characterizes the "updates" a UDT-like agent will happily defer to? It is NOT just its own exact prior (UDT accepts real improvements), but not arbitrary endorsement either. Seek an endorsement-LIKE concept (a generalization) capturing "updates UDT defers to". Use the principal's Geometric UDT conjecture: more updateful about moral uncertainty / human values, more updateless about other matters. Relate to UDT1.0-believes-it's-UDT1.1 (see the Cole thread). Radical-probabilist "superconditioning" may bridge endorsement (no evidence index) to updates.`,
    deepenFocus: `Propose a precise generalized-endorsement relation "A updatelessly-defers to B" that (i) reduces to ordinary endorsement in the updateful/no-acausal case, (ii) correctly does NOT hold for the future self that caves to counterfactual mugging, and (iii) DOES hold for genuine improvements UDT accepts. Give 2-3 discriminating examples (counterfactual mugging, transparent Newcomb, a benign update) and show your relation classifies them correctly. State the UDT1.0/UDT1.1 deference theorem schema precisely.`,
  },
  {
    key: 'unbounded-embedded-agency',
    title: 'Unbounded embedded agency (Cole Wyeth) & UDT1.0/1.1 optimality',
    seed: `Cole Wyeth's reflective-oracle AIXI uses EDT on single actions and learns its own decision procedure empirically (source code unknown, behavior of any code known). Main result: (1-δ)-confidence in your decision procedure ⇒ ε-optimal. Principal's critiques: (a) IMPROBABLE ACTIONS — confidence in source code forces tiny probability on un-taken actions; reasoning about them needs contrived worlds; can spurious-proof / Troll-Bridge-like pathologies recur even without explicit source-code knowledge? (b) the self-knowledge assumption SNEAKILY rules out self-modification (and thus environments where updateless reasoning is needed and reachable via self-mod). (c) reflective-oracle independence makes Omega-prediction look impossible, and the ε-optimality notion interleaves conditionals so updateful behavior always looks fine ("AIXI converges to AIXI"). Principal's proposed fix: theorem "if a UDT1.0 agent (1-δ)-believes its policy is UDT1.1, then it is ε-optimal" — belief-you're-UDT1.1 does the work of Cole's hand-constructed oracle (avoiding self-coordination/Stag-Hunt bad equilibria).`,
    deepenFocus: `Develop the UDT1.0-believes-UDT1.1 ⇒ ε-optimal conjecture into a precise statement: define UDT1.0 (per-action) and UDT1.1 (whole-policy, trivially optimal under source-code certainty), the optimality notion, and the role of the (1-δ) belief in dissolving Stag-Hunt self-miscoordination. Separate the "self-knowledge" assumption into a self-component and an environment-component so it stops covertly banning self-modification. Note exactly where this is Vingean (trust UDT1.1 on general principles, not by predicting it) and how it relates to tiling.`,
  },
]

// Pipeline: ideate -> deepen -> red-team, per thread, no barriers. (No Lean compilation here.)
const threadWork = pipeline(
  THREADS,
  (t) => agent(PREAMBLE + `
TASK (Ideate — thread "${t.title}").
${t.seed}

Produce 4-7 CONCRETE, formalizable research ideas for THIS thread, each as: a crisp candidate
proposition/definition; why it bears on "when can humans justifiably trust AI"; the cleanest formal
setting; how hard it looks; and which single idea is the most promising to develop. Cross-connect to
the v2 §10 modularization wherever the thread touches LI deference. Write ${LAB}/findings/${t.key}-ideate.md
and return a ~150-word summary naming your top pick.`,
    { label: `ideate:${t.key}`, phase: 'Ideate' }),

  (ideateSummary, t) => agent(PREAMBLE + `
TASK (Deepen — thread "${t.title}"). Your own ideation produced:
"""${ideateSummary}"""
Now DEVELOP the most promising idea into a precise toy formal model. ${t.deepenFocus}
Be explicit about every hypothesis. Give at least one fully worked micro-example (small enough to
check by hand or by a short Python/sympy script you may write and RUN under ${LAB}/ — Python is cheap,
unlike Lean). State the central claim as PROVED / SKETCHED / CONJECTURE and, if sketched, give the
proof skeleton and name the gap. If a small piece looks Lean-checkable, write a CANDIDATE Lean file
under ${LAB}/lean/${t.key}.lean (from the Template; targeted imports; do NOT compile it yourself —
mark UNCHECKED for the Lean-verify agent). Write ${LAB}/models/${t.key}-model.md; return a ~150-word
summary including the central claim and its status.`,
    { label: `deepen:${t.key}`, phase: 'Deepen' }),

  (modelSummary, t) => agent(PREAMBLE + `
TASK (Red-team — thread "${t.title}"). The deepened model:
"""${modelSummary}"""
Adversarially STRESS it. Read ${LAB}/models/${t.key}-model.md. Hunt for: (a) is the central claim
actually TRUE — find a counterexample or a degenerate case (a short Python check is fine and
encouraged); (b) does a stated hypothesis secretly smuggle in the conclusion (vacuity / triviality);
(c) if there is a candidate Lean file, by careful READING (do not compile) predict whether it would
type-check AND whether the statement faithfully captures the informal claim — quantifiers, hypotheses,
not-provable-for-the-wrong-reason — and leave precise notes for the Lean-verify agent; (d) what is the
smallest change that would make a false claim true, or a true-but-vacuous claim substantive? Write a
candid verdict to ${LAB}/redteam/${t.key}-redteam.md: SOLID / SALVAGEABLE (with the fix) / BROKEN
(why), plus the single most valuable next step. Return a ~120-word verdict.`,
    { label: `redteam:${t.key}`, phase: 'Red-team' }),
)

// Lean correspondence audit of the EXISTING code (cross-cutting, READ-ONLY — no recompiling).
const auditWork = (async () => {
  const mapped = await agent(PREAMBLE + `
TASK (Lean-audit, stage 1 — MAP). Read lean-deference/LeanDeference.lean in full and the v2 doc §9
(the "Machine-check" section) plus the informal claims those Lean theorems are meant to back (§3
proof, §5.2 collapse, §0.3 theorem statements). For EACH Lean declaration (decomposition,
value_of_defects, soft_nonneg, value_of_CM, the Approx/AsympLE calculus lemmas, value_asymptotic,
softmax_lower_bound, CM_implies_immodest) write: the exact Lean statement (hypotheses + conclusion in
plain words), and the precise informal claim from the v2 doc it is supposed to capture. Flag any where
the mapping is non-obvious. (Do NOT recompile — the build is already confirmed sorry-free with axioms
[propext, Classical.choice, Quot.sound].) Write ${LAB}/audit/lean-map.md. Return a ~150-word summary.`,
    { label: 'lean-audit:map', phase: 'Lean-audit' })

  return agent(PREAMBLE + `
TASK (Lean-audit, stage 2 — ADVERSARIAL VERIFY, read-only). The map:
"""${mapped}"""
Now adversarially check, declaration by declaration, whether each Lean theorem ACTUALLY captures its
informal claim. For each, ask: are the hypotheses faithful or stronger-than-stated (smuggling the
conclusion)? Is it vacuous/trivial (e.g. an identity that holds for any inputs, presented as if it
encoded a deference fact)? Do the Lean quantifiers match the prose ("for all frames" vs "for some")?
Is value_asymptotic's set of hypotheses exactly the 5 LI theorems (so it's an honest "modulo the LI
results" claim) and nothing more? Is CM_implies_immodest's hypothesis the genuine CM identity or a
disguised restatement of immodesty? The crucial subtlety to weigh: the v2 doc ITSELF says (§9) that
the Lean checks the proof's *algebra and finite core*, NOT that the LI theorems force the defects to
0 — judge whether v2 §9 honestly states these limits. Write ${LAB}/audit/lean-correspondence-verdict.md
with a per-declaration FAITHFUL / OVERSTATED / VACUOUS / MISLEADING rating and an overall verdict on
whether v2 §9's claims are honest. Return a ~150-word verdict.`,
    { label: 'lean-audit:verify', phase: 'Lean-audit' })
})()

// Lateral / creative single agent (cross-cutting).
const lateralWork = agent(PREAMBLE + `
TASK (Lateral / creative). Cover the agenda's less-LI-central items AND hunt for non-obvious
cross-connections. Specifically: (1) "What is a decision problem?" — the principal typed a decision
procedure as (S,A)→A but notes the two A's differ (set vs element) and it wants a dependent type;
give the clean dependently-typed formalization and relate the "systematized winning / why-ain'cha-rich"
optimality notion to tiling and to the endorsement/deference picture. (2) Vingean agency & abstraction
— "we can't predict the chess master's moves but can predict they'll win"; propose how a theory of
abstraction could characterize Vingean agency, and connect it to the Blackwell/Geanakoplos "trust on
general principles" already used in v2 §1.1. (3) The "size problem" — principal/agent are modeled
asymmetrically (principal's beliefs given, agent's uncertain over a FINITE set); what breaks when they
recursively model each other or themselves, and does the LI/self-reference picture fix it? (4) At least
3 genuinely lateral wildcard ideas connecting two agenda threads that the other agents are unlikely to
surface. Flag claims by status. Write ${LAB}/findings/lateral.md; return a ~150-word summary.`,
  { label: 'lateral', phase: 'Lateral' })

// Run threads + audit + lateral concurrently (none compile Lean → RAM-safe).
const [threads, audit, lateral] = await Promise.all([threadWork, auditWork, lateralWork])

// ---------------------------------------------------------------------------
// Serial Lean verification: the ONLY agent allowed to compile (one process at a time -> fits 7GB RAM).
phase('Lean-verify')
const leanVerify = await agent(PREAMBLE + `
TASK (Lean-verify) — you are the ONLY agent permitted to run Lean. You have the machine to yourself
now; still, compile ONE file at a time (each load uses ~1-3 GB of the 7 GB RAM; never run two checks
concurrently).
1. List the candidate Lean files: \`ls ${LAB}/lean/*.lean\` (ignore Template.lean and check.sh).
2. For EACH candidate, one at a time:
   - Read it and the model file that motivated it.
   - Run: \`bash ${LAB}/lean/check.sh <absolute path>\` (allow up to ~5 min; targeted imports load in ~1 min, but the first compile of the run may be slower).
   - If it fails only on a renamed import, fix the import (use the find-olean trick in Template.lean) and re-check. If it fails on the proof, either repair it if quick, or REDUCE the claim to the largest piece that DOES check (e.g. drop to the algebraic identity), or replace the proof body with \`sorry\` and record it as UNPROVEN. Do not fake a check.
   - Record: does it compile? \`#print axioms\` output (any \`sorryAx\` ⇒ NOT verified)? AND — most important — does the checked statement FAITHFULLY capture the informal claim from its model file, or is it weaker/vacuous?
3. If NO usable candidates exist, instead author ONE small, genuinely-checked lemma yourself for the
   most crisp conjecture in the models (e.g. the cross-agent / merging-inductor algebraic core, or the
   soft-vs-hard liar split), starting from Template.lean — and honestly report what it does and does
   NOT establish.
Write ${LAB}/audit/lean-verify-report.md: per-file [COMPILES? | axioms | faithful-to-claim?] plus an
honest overall statement of what is now machine-checked vs still informal. Return a ~150-word summary.`,
  { label: 'lean-verify', phase: 'Lean-verify' })

// ---------------------------------------------------------------------------
phase('Synthesis')
const synth = await agent(PREAMBLE + `
TASK (Synthesis). Read EVERY file under ${LAB}/findings/, ${LAB}/models/, ${LAB}/redteam/, and
${LAB}/audit/ (list them, then read them). Produce ${LAB}/report/RESEARCH-REPORT.md — the deliverable
the principal will use to plan summer research. Include:
1. Executive summary (the through-line: trust between rational agents → human-AI trust, and where LI
   gives the most leverage).
2. A RANKED table of the candidate research directions surfaced, with: crisp statement, status
   (PROVED/SKETCHED/CONJECTURE/BROKEN per the red-teams), bearing on the human-AI-trust question,
   formal setting, and estimated tractability over a summer.
3. The 2-3 most promising directions written up in detail (pulling the best from the models), each
   with the cleanest precise conjecture and a concrete Lean target (noting what the Lean-verify agent
   already machine-checked vs what remains informal).
4. The Lean situation: the existing LeanDeference.lean is confirmed sorry-free; summarize the
   correspondence audit's bottom line (is v2 §9 honest? any overstated/vacuous theorems?) and what new
   Lean (if any) got checked this run.
5. A concrete suggested summer plan / sequence of bite-sized formalizable steps.
6. Open problems and the most important unknowns.
Return a ~250-word executive summary.`,
  { label: 'synthesize', phase: 'Synthesis' })

const critique = await agent(PREAMBLE + `
TASK (Completeness critic — adversarial). Read ${LAB}/report/RESEARCH-REPORT.md and the underlying
files. Your job is to find what is MISSING, HAND-WAVY, or LIKELY WRONG — be a harsh referee:
- Which "conjectures" are probably false or already-known? Which "results" are vacuous?
- Where does an informal claim lack any path to formalization? Where does a Lean claim NOT match its
  informal statement (re-examine the audit and the Lean-verify report)?
- Which agenda items got shallow treatment? Which cross-connections were missed?
- Is the merging-inductors (Fast Student/Slow Teacher) story actually load-bearing, or did it get
  hand-waved at the crucial step (B_t being a genuine inductor; H endorsing B)?
- What is the single most important thing the principal should NOT believe without more work?
Write ${LAB}/report/CRITIQUE.md with prioritized, specific criticisms and concrete fixes. Return a
~200-word summary of the top criticisms.`,
  { label: 'critique', phase: 'Synthesis' })

log('Deference/trust lab complete. See ' + LAB + '/report/RESEARCH-REPORT.md and CRITIQUE.md.')
return {
  orientation: String(orientation).slice(0, 400),
  threads: (threads || []).map(String).map(s => s.slice(0, 200)),
  audit: String(audit).slice(0, 400),
  lateral: String(lateral).slice(0, 300),
  lean_verify: String(leanVerify).slice(0, 500),
  report_summary: String(synth).slice(0, 1200),
  critique_summary: String(critique).slice(0, 1000),
}
