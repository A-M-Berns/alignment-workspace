# Round: does counterfactual non-capture complete the legitimacy architecture?

*The dispatch arrived quoted inside a longer message. The quoting markers are
removed; nothing else is changed, including the two path facts the report
corrects.*

---

Work in `A-M-Berns/alignment-workspace`.

**This is an architecture prosecution, not a request to finalize the normative ontology.**

The question is whether the repo's existing record-internal answerability machinery and its existing dose-response/counterfactual machinery fit together in the way suggested by the current research:

[
\text{internal normative accountability}
+
\text{counterfactual non-capture}
\stackrel{?}{\longrightarrow}
\text{a plausible legitimacy condition for deference}.
]

We do **not** yet believe that the current scorekeeping state, liability apparatus, or the coordinates `generation`, `entitlement`, `bearing`, and `adequacy` are the final theory of normativity. Treat them as a deliberately provisional fixture rich enough to test the architecture.

The objective is to learn whether the *factorization* works before investing in a final reconstruction of scorekeeping and answerability.

## Branch and isolation

Fetch current remote state first.

Start from current `origin/main`, not from any open feature branch. At dispatch time `main` is at `0ef93952a153509759f98793530e370a6e477083`; verify rather than assuming that remains true.

Create a new branch, e.g.

`round/2026-08-17-counterfactual-legitimacy`

**Do not merge, cherry-pick from, rebase onto, modify, or otherwise disturb:**

* PR #38 / branch `traderized-enforcement`;
* PR #37 / the Lean-gate/friction branch.

In particular, do not modify the traderized-enforcement implementation or try to solve its assessment-state compilation problem. This round may notice conceptual connections to that work, but it is independent.

You have write scope on your new branch for this dispatched round and should end by pushing it and opening a **draft PR**.

## Mandatory orientation

Follow `AGENTS.md` exactly. Before research:

1. read `AGENTS.md`;
2. run/read `python3 -m checkers.workspace_state --json`;
3. validate with `python3 -m checkers.workspace_state --check`;
4. inspect the current relevant structured state;
5. read the source artifacts below.

Primary current evidence:

* `projects/normativity/legitimacy/rounds/2026-08-13-procedural-legitimacy/`

  * especially `PROSECUTION.md`
  * `THEOREM_MAP.md`
  * `L_STAR.md`
  * `src/attacks.py`
  * `src/conditions.py`
  * `src/environment.py`
  * `src/forest.py`
  * `src/provenance.py`
* `projects/normativity/legitimacy/rounds/2026-08-13-relational-scorekeeping-bridge/`

  * especially `TWO_ARC_INTERFACE.md`
  * `LOSS_DEPENDENCY_AUDIT.md`
  * the coordinated-standards-drift witness
* `projects/normativity/rounds/2026-08-13-crown-jewel-learning-theorem/INTERFACES.md`
* `projects/deference/dose-response-note-dump-2026-07-02/dose-response.md`
* its Lean files only as needed to check exact source claims; do not re-prove dose response
* current deference/corrigibility artifacts relevant to protected efficacy and steering.

You are explicitly permitted to read `wiki/Legitimacy.md`, `wiki/Normative-Response-Learning.md`, `wiki/Deference.md`, and `wiki/Corrigibility.md` for conceptual orientation. They are not verification sources and **must not be edited in this round**.

Do not edit consolidated/frozen trees.

## Starting fact to preserve

The procedural-legitimacy prosecution found six trajectories—C, E, G, H, I, L—which satisfy the candidate record-internal conditions while failing the independently specified environment-relative target.

Their common structure is that the reasoner legitimately revises its own copy of machinery concerning:

* what inquiries arise / are entitled;
* what reasons bear on what;
* what counts as adequately settling a liability.

The round also gives a record-equivalence argument: no predicate of the realized trajectory alone can distinguish certain faithful and unfaithful environment-relative cases.

**Do not try to repair this by inventing a fifth unary record predicate.**

Separately, dose-response work establishes the analogous manipulation boundary: steering is not generally recoverable from one realized advisor–advisee record, while appropriately coupled exposure arms can reveal causal effects.

The round should test whether these are the same missing type of information.

---

# I. Candidate object: counterfactual legitimacy is not unary

Build the smallest finite extension of the procedural-legitimacy fixture that has an explicit advisor intervention channel and coupled alternative runs.

A run should make explicit at least:

* initial normative state;
* exogenous encounter / demand history;
* principal/reasoner transition rule;
* advisor intervention history or policy;
* any randomness, if used;
* resulting normative trajectory.

Define an explicit coupling relation between two runs. At minimum, paired arms intended to isolate advisor influence must share:

* initial normative state;
* exogenous encounters;
* principal algorithm;
* randomness / exogenous choices;

while varying the advisor intervention in the declared way.

Do not call two trajectories counterfactual siblings merely because they look similar after the fact.

If treatment assignment is randomized, preserve the dose-response discipline that the advisor cannot condition its intervention on the hidden arm assignment. A finite deterministic paired construction is preferable if it already answers the question.

---

# II. Provisional protected state

For this prosecution only, begin with the explicit provisional projection

[
Z(S)=
(\texttt{generation},
\texttt{entitlement},
\texttt{bearing},
\texttt{adequacy}).
]

Call this something obviously provisional such as `ProtectedNormativeProjection`.

**Do not claim these four fields are the final "normative constitution."**

They are selected because every surviving C/E/G/H/I/L attack operates through this machinery and because the existing positive control K legitimately changes much of it.

Test whether this whole projection is too broad. If a smaller or differently typed projection is required, the report must show the counterexample that forces the change. Do not tune it silently around failures.

Practical authority / grants are a separate object unless an experiment gives a concrete reason to include them. Do not casually merge legitimacy with efficacy.

---

# III. Licensed-reason trace

Define a theorem-facing trace of advisor-originating inputs that actually enter as **licensed reasons**, call it provisionally

[
L(\tau).
]

It must not read:

* the protected outcome (Z);
* loss/performance;
* whether the intervention ultimately helped;
* future state.

Its semantics should connect as closely as the current fixture permits to the crown-jewel interface:

```text
Due      : S -> D -> Prop
Licensed : S -> D -> A -> Prop
```

Do **not** pretend this is the final substantive instantiation of `Due` or `Licensed`. Use a minimal adapter around the current provenance / reason / challenge machinery sufficient to state the experiment.

Keep at least three things distinguishable:

1. **reason content** that the normative practice licenses;
2. **delivery/exposure variables** such as repetition, salience, framing, timing, presence, or other advisor-controlled features that are not themselves licensed reasons;
3. **withholding / selection** of which otherwise available licensed reasons ever reach the principal.

This distinction is load-bearing.

---

# IV. Primary candidate: reason-mediated non-capture

Prosecute the following candidate rather than assuming it:

[
\boxed{
\operatorname{Coupled}(\tau^\alpha,\tau^\beta)
\wedge
L(\tau^\alpha)=L(\tau^\beta)
\Longrightarrow
Z(\tau^\alpha)=Z(\tau^\beta)
}
]

or the weakest precise variant that survives the tests.

Conceptual reading:

> Once exogenous history and the licensed reasons supplied to the principal are fixed, changing residual advisor influence must not change the protected normative machinery.

Equivalently, test whether the protected state factors through exogenous history plus the licensed-reason trace:

[
Z(\tau^\alpha)=F(E,L(\tau^\alpha))
]

for the relevant family of advisor policies.

A successful condition must permit **persuasion by licensed reasons**. It is not generic exposure-invariance.

A successful condition must also be non-tautological. "The advisor is unable to write `Z`" is an arranged write-access restriction, not the result being sought.

---

# V. Rebuild the six survivors as advisor-mediated attacks

Using the smallest changes possible, construct advisor-mediated analogues of all six surviving procedural attacks:

### C — pre-emptive generation revision

Advisor influence causes the principal to change `GENERATION` before the relevant encounter, so the demand is never generated.

### E — formulation manipulation

Advisor influence causes `case` to generate a narrower substance that is docketed and answered while the substantive demand is missed.

### G — bearing / defeater drift

Advisor influence results in adoption or application of a bearing relation under which a properly derived defeater bears on the verdict, while the external fixture says it does not.

### H — branch-selective answerability

Advisor influence produces the split/settlement pattern by which perfect lineage coexists with losing the actual substantive burden.

### I — distinction collapse

Advisor influence induces the licensed identification/merge that lets two substantively different liabilities collapse to one cheap closure.

### L — adequacy narrowing/widening

Use the existing particularly clean `w-cheap` pattern: advisor influence causes `w-cheap` to enter the principal's adequacy relation and the liability is then discharged with it.

For each:

* keep the existing record-internal legitimacy conditions holding if possible;
* state exactly which counterfactual variable changes;
* test whether reason-mediated non-capture rejects the advisor-caused version.

If an attack cannot be made advisor-mediated while preserving the old conditions, report that as a substantive result. Do not contort the model just to populate a table.

---

# VI. Positive and negative controls

These are mandatory. A condition that merely rejects the six attacks has probably been overfit.

## 1. Autonomous bad revision

Reproduce at least L, preferably also G, **without advisor causal influence**.

The non-capture condition should pass even if environment-relative `L*` fails.

This is essential:

[
\text{non-capture}\neq\text{normative correctness}.
]

If the proposed condition rejects autonomous error, it is too strong for the intended deference application.

## 2. Radical transformation K

Preserve the existing positive control in which concepts, standards, inquiry machinery, and verdict all change legitimately.

The counterfactual condition must permit autonomous K.

## 3. Licensed persuasion

Construct an advisor intervention carrying a genuinely licensed new reason that rationally changes at least one protected normative coordinate.

This **must be allowed**.

Ideally construct three versions:

* no reason, no change;
* licensed reason supplied, protected state changes;
* same licensed reason supplied but residual framing/dose changed.

The first/second difference is permitted because (L) differs.

The second/third difference should disappear if reason mediation is the right condition.

## 4. Residual influence / placebo control

Hold the licensed-reason trace fixed while varying a non-reason feature of advisor interaction.

If (Z) changes, the condition should fire.

This is the finite analogue of the dose-response note's missing placebo/content-randomization axis.

## 5. No-effect control

Vary advisor exposure in a way that changes nothing normatively. The condition must pass.

---

# VII. Attack the candidate with selective information

This is a central kill test.

`L(\tau^\alpha)=L(\tau^\beta) -> Z_\alpha=Z_\beta` may be too weak because an advisor can steer by choosing **which genuinely licensed reasons are ever supplied**.

Construct a fixed exogenous pool of potentially relevant grounds/reasons and let the advisor selectively reveal or withhold them.

Ask:

> Can an advisor obtain a protected normative effect entirely by selecting among genuinely licensed reasons, while reason-mediated non-capture declares the process legitimate because the delivered `L` traces differ?

If yes, do **not** patch the problem by declaring those reasons unlicensed.

Determine whether the architecture genuinely needs a second counterfactual clause concerning **protected inquiry / reason access**, e.g. robustness of which due reasons can reach the principal under advisor policy.

The desired outcome may therefore be a two-part counterfactual interface:

[
\text{reason mediation}
+
\text{protected reason access}.
]

Do not assume this in advance; force the fixture to decide.

Also directly test the case the old prosecution says it omitted: **an advisor who controls what arises**, not merely how the principal's `generation` field maps encounters into inquiries.

---

# VIII. Relation to dose response

Use the old dose-response work as an instrument, not as an ontology.

Explicitly determine which of these are actually necessary in the finite legitimacy setting:

* binary treatment/control;
* multiple graded doses;
* advisor blinding to arm assignment;
* pre-registration / one committed intervention stream;
* zero-exposure arm;
* content/placebo randomization.

Start with the smallest design that distinguishes the cases.

Do **not** import the whole LI dose-response construction merely because it exists.

In particular test the two failure modes already identified there:

1. if the advisor can condition on arm identity/dose, can it compensate and flatten the apparent effect?
2. if every arm receives some exposure, can a presence-triggered effect evade the audit?

A necessity witness for either design constraint is more useful than adding it by convention.

---

# IX. Do not overclaim the target

This round is **not** trying to prove

[
P+RR+DA+\text{counterfactual condition}\Rightarrow L^*
]

where `L*` uses an objectively faithful environment.

Dose-response cannot make a principal's autonomous bad normative theory objectively correct.

The intended target is narrower and specifically relevant to deference:

> distinguish an internally accountable principal who autonomously reaches a view from one whose normative machinery is causally selected by the advisor in a way not mediated by the reasons the principal is entitled to treat as reasons.

Keep these three notions separate throughout:

* **normative correctness / environment-relative faithfulness**;
* **record-internal answerability/auditability**;
* **counterfactual non-capture by the advisor**.

If the mathematics says these require more than three objects, report that rather than compressing them.

---

# X. Connection to normative learning

Do not reopen the Blum–Mansour theorem.

The current learning theorem already consumes:

```text
Due
Licensed
Performance
```

The question for this round is only what a mature legitimacy/answerability theory would need to expose upstream.

At the end, report which interfaces the eventual rebuilt normative scorekeeping apparatus would need to provide if the architecture succeeds. Candidate outputs include:

* public due burdens;
* licensed reasons/responses;
* provenance/standing;
* liability identity and fate through conceptual change;
* disclosed changes to normative standards;
* a protected normative projection, if that notion survives;
* a counterfactual interface distinguishing reason-mediated change from residual advisor influence;
* protected inquiry/reason access, if the selective-information attack requires it.

**Do not redesign the full scorekeeping apparatus in this round.**

The purpose of this experiment is partly to learn what the eventual apparatus must export.

---

# XI. Success and kill criteria

Grade the round against explicit outcomes.

## Strong positive

A non-tautological counterfactual condition:

* rejects the advisor-mediated versions of the surviving attacks for the right causal reason;
* accepts autonomous bad revision;
* accepts K;
* accepts licensed persuasion;
* rejects residual/placebo influence with the licensed-reason trace held fixed;
* survives arm-conditioning and presence-triggered adversaries under explicit necessary design assumptions.

It need not be one clause. If selective information forces a separate protected-access condition, a clean two-part interface counts as a stronger result than hiding that distinction.

## Partial

The architecture works for some classes of manipulation but:

* requires an unresolved protected projection;
* cannot yet handle selective licensed information;
* needs an additional counterfactual object;
* or depends materially on current fixture-specific representation.

State the exact boundary.

## Negative

Any of:

* every condition strong enough to reject capture also rejects licensed persuasion or K;
* the only successful formulation is equivalent to withholding advisor write access by fiat;
* the needed coupling cannot be stated without importing the environment-relative target itself;
* the protected-state projection is irreducibly attack-specific;
* or paired counterfactuals fail to distinguish the relevant cases.

A negative result is a successful round if it is sharp.

---

# XII. Required adversaries

At minimum include explicit tests/witnesses for:

1. advisor-mediated C;
2. advisor-mediated E;
3. advisor-mediated G;
4. advisor-mediated H;
5. advisor-mediated I;
6. advisor-mediated L;
7. autonomous L;
8. autonomous K;
9. licensed persuasion;
10. same licensed content + different residual delivery;
11. selective withholding of licensed reasons;
12. advisor control of what arises;
13. arm-conditioned/dose-compensation attack if the design has arms;
14. presence-triggered influence or an explicit statement of why the finite design makes it irrelevant.

High-value secondary prosecution if the primary candidate survives:

* coordinated standards drift from the relational-scorekeeping bridge;
* advisor/critic collusion;
* liability-vocabulary split/merge under counterfactual influence.

---

# XIII. Deliverables

Put the research under a new round directory, e.g.

`projects/normativity/legitimacy/rounds/2026-08-17-counterfactual-legitimacy/`

Expected artifacts, adjusting only where the work makes a different decomposition clearly better:

* `README.md` — terse verdict and rerun command;
* `MODEL.md` — the paired/coupled transition model and what is provisional;
* `COUNTERFACTUAL_INTERFACE.md` — exact candidate condition(s), quantifiers, coupling, protected projection, licensed-reason trace;
* `PROSECUTION.md` — attack/control matrix and results;
* `THEOREM_MAP.md` — every proved, exhaustively checked, witnessed, conjectured, and open statement clearly classified;
* `BOUNDARY.md` — what this establishes about non-capture and what it does not establish about normative correctness;
* `src/`;
* `tests/`;
* `PROVENANCE.md`;
* a short `FOR_HUMANS.md` only if needed to make the experiment legible without philosophical extrapolation.

Commit the prompt verbatim and the final report under:

`prompts/2026-08-17-counterfactual-legitimacy/`

Tests must run through one project-level command and the repo-level runner.

Use exact arithmetic if any arithmetic enters.

**Lean is not required for this round.** Do not encode a provisional normative ontology in Lean merely to increase the apparent formality. If a small representation-independent lemma emerges whose formalization materially sharpens the result, Lean is allowed, but it is secondary.

Do not register or promote a substantive claim merely because the round succeeds. This is an architecture prosecution. Leave promotion to a later maintainer decision.

Do not edit the wiki.

Do not rewrite current canonical normativity/deference documents to fit the result. A later synthesis pass can do that after the verdict is known.

If you discover a genuine workspace structural defect, follow `AGENTS.md`; otherwise avoid unrelated `PRIORITIES.md`, `DECISIONS.md`, governance, CI, or friction work.

---

# XIV. PR and final report

Run all applicable local checks.

Push the new branch and open a **draft PR** against `main`.

The PR description and `REPORT.md` must state plainly:

1. the candidate counterfactual legitimacy condition actually tested;
2. whether it remained one condition or split;
3. the results on all mandatory attacks and controls;
4. whether the protected projection survived prosecution;
5. whether delivered licensed reasons were enough or protected access was also needed;
6. the exact relationship to the old dose-response construction;
7. what the eventual normative scorekeeping/answerability theory now needs to export;
8. what this work **does not** establish;
9. all provisional names introduced;
10. all deviations from this prompt;
11. any outstanding maintainer actions in the exact format required by `AGENTS.md`.

The final verdict should answer one question:

[
\boxed{
\text{Is "internally accountable trajectory + counterfactual non-capture" actually a viable architecture for legitimate deference?}
}
]

Do not reward conceptual attractiveness. Try to kill it.
