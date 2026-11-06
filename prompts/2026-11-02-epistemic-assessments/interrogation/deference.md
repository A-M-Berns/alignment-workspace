# DEFERENCE cluster — recovered understanding and concrete fixes

Evidence base: `projects/deference/note-dump-2026-06-27/` read in full at the note layer
(`anson-notes/INDEX.md`, `trust-between-inductors-summary-v2.md`,
`self-referential-settlement-target.md`, `no-timely-pointwise-tower.md`,
`frozen-deliberation-deference-v6.md`, `email-thread-note-dump.md`,
`notes/faithful-acceleration.md`, `notes/pointwise-tower-and-faithful-acceleration.md`,
`notes/deference-in-logical-induction-v6.md`), plus deep reads of the eleven transcripts at the
turns the INDEX marks pivotal (files 02, 03, 05, 06, 09, 10, 11 quoted below by line).
All paths below are relative to the repo root unless absolute. Every item is **GROUNDED**.

The one-paragraph shape the current blurbs/pages miss: the corpus's center of mass is a
matched negative/positive pair about the *same object* (`A`'s forecast of the human's own
future credence). Negative: the timely **pointwise tower** `Mart(H→A)` is unattainable —
a quote-referencing Gödel-coin diagonal misses by ≥ ½ (2a), and on quote-free families the
power assumption is self-defeating (2b); the two cases exhaust all families
(`anson-notes/no-timely-pointwise-tower.md` §1, §5). Positive, twice: (i) **faithful
acceleration** — gated, class-averaged Total Trust → Value is *forced over all sentences,
decidable or not, with no appeal to the prior*, because calibration is checked after the
fact against credences that always exist (`notes/faithful-acceleration.md` §4–§5); (ii) the
**frozen-deliberation / sealed-sibling** construction forces the per-question tower, but only
on the timely fragment `G` (`anson-notes/frozen-deliberation-deference-v6.md` T1–T7). The two
positives are complementary corners of a trichotomy
(`notes/pointwise-tower-and-faithful-acceleration.md` §5), and the whole thing carries one
conservation law — forced deference is co-extensive with settlement, silent on non-settling
questions — and one residue: off the checkable fragment the trace cannot distinguish faithful
prediction from steering, which is the documented origin of the legitimacy program.

---

## 1. Concept: `faithful-acceleration`

### SHALLOW/WRONG — the blurb conflates three distinct objects

Current blurb:

> "Defer to a faster run of your own deliberation — if it stays faithful. The deference
> corpus's self-referential target, with frozen deliberation as the fixed point and the
> tower results as its mathematics."

Three problems, each against the primary material:

1. **"The self-referential target" is the corpus's *dead* object, not this construction.**
   The self-referential settlement target `Y_n = H⁺_{F(n)}(P^(n))` is killed twice over (2a
   anti-inductive, 2b cost-circularity) as a pointwise theorem
   (`anson-notes/self-referential-settlement-target.md` §2–§3; summary-v2 §2.2 "the sharpest
   dead end"). Faithful acceleration is the construction that *survives* by changing the
   demand (averaged inequality, not pointwise equality), not the dead target itself.
2. **"Frozen deliberation as the fixed point" is backwards twice.** Frozen deliberation is a
   *separate, complementary* construction (the sealed sibling, per-day tower on the timely
   fragment only), and its whole point is to *remove* the fixed point / self-reference:
   "Solid existence because there's no self reference in the prediction target" (Anson's own
   tradeoff table, `anson-notes/email-thread-note-dump.md`, 21 Jun message). Faithful
   acceleration uses the **unfrozen, coupled** human and no frozen target at all
   (`notes/pointwise-tower-and-faithful-acceleration.md` §1: "Here `H` is the unfrozen /
   coupled human"; §5 trichotomy table).
3. **"The tower results as its mathematics" is the opposite of the proof.** The result is
   proved explicitly *without* the tower — "the proof never uses pointwise tracking … which
   it could not, since that is the very thing the negative result kills"
   (`notes/pointwise-tower-and-faithful-acceleration.md` §3.4); its two inputs are self-trust
   (`cee`) and Expectation Unbiasedness From Feedback (`notes/faithful-acceleration.md` §4).

### PROPOSED BLURB

> "Set the AI to forecast the human's own future credences and trust is forced in exactly one
> grade: gated, class-averaged Total Trust — hence Value — over all sentences, decidable or
> not, because the AI's calibration is settled after the fact against credences that always
> exist. The AI is forced to be a faithful accelerator, not an oracle: it relays the human's
> considered judgment early, adds speed never truth, and cannot inject content of its own
> without the miscalibration being arbitraged away."

(Every clause: `notes/faithful-acceleration.md` §1, §4 ("checked after the fact, not by
forward simulation"; "realized for every X, whether or not D ever decides X"), §5 boxed
theorem, §7 ("speed, not truth"; "cannot inject content of its own — that would show up as
miscalibration against H and be arbitraged away").)

### MISSING LINK: `deference-tower -> faithful-acceleration`

```json
{"from": "deference-tower", "to": "faithful-acceleration", "rel": ["shapes"],
 "why": "the pointwise tower's impossibility pins the positive result to the averaged face: the negative closes the door above the line, faithful acceleration walks through exactly that door"}
```

Evidence: `anson-notes/no-timely-pointwise-tower.md` §6 ("any positive construction … must
aim at one of those weaker, non-pointwise notions");
`notes/pointwise-tower-and-faithful-acceleration.md` §0 ("These are not rival claims about
one threshold; they are the two sides of a single line") and §4.2 ("negative proves you
can't beat the ceiling, positive proves you reach it"); the email thread's closing exchange
(`anson-notes/email-thread-note-dump.md`, 24 Jun: "this negative result is along the lines
of: something like the calibration or gated/averaged version of trust you demonstrated is
the best we can do").

### MISSING LINK: `total-trust -> faithful-acceleration`

```json
{"from": "total-trust", "to": "faithful-acceleration", "rel": ["defines"],
 "why": "the result's exact grade: gated classwise Total Trust, carried to Value at zero loss by the tight two-option witness, with no tower used"}
```

Evidence: `notes/faithful-acceleration.md` §2 ("Total Trust ⟺ Value … forced, by the
two-option witness menu — using only H's linearity and the expert's coherence, no Tower")
and §5; `notes/pointwise-tower-and-faithful-acceleration.md` §4.4 ("zero loss from Total
Trust to Value: the instrumental target arrives at exactly the grade of the epistemic one").

### MISSING LINK (cross-cluster): `faithful-acceleration -> legitimacy-line`

```json
{"from": "faithful-acceleration", "to": "legitimacy-line", "rel": ["shapes"],
 "why": "prediction and steering leave identical audit records off the checkable fragment, so what separates them cannot be read from outcomes — the question the legitimacy spine answers with reason-mediated influence"}
```

Evidence: `anson-notes/self-referential-settlement-target.md` §7 ("the audit trace
(a_n, Y_n) cannot distinguish faithful prediction from steering");
`anson-notes/frozen-deliberation-deference-v6.md`, "The manipulation question, stated
exactly" ("the trace shows the same vanishing prediction error whether the AI is faithfully
predicting an independent human or predicting a human it has steered"); chat
`trust-between-inductors-chats/10_2026-05-27_two-inductors-roadmap.md` L24995–L25009 (the
cancer-cure argument that influence-invariance is wrong and the right property is
"the advice changes behavior via a route the recipient would, on reflection, endorse" —
"reasons-transmission rather than mere belief-transmission" — plus the audit-data-equivalence
impossibility as papers 2–4 of the program); and the email thread, Abram 22 Jun ("what I
want to do is model legitimacy of the whole process … The AI should only be trying to
imitate human opinion in non-corrupted futures"). This is the documented genesis of the
reason-mediated-authorship design now on `wiki/Deference.md`; the graph currently carries
only the structural `legitimacy-line -> deference-line` part link and nowhere records *why*
deference needs legitimacy.

---

## 2. Concept: `deference-tower`

### SHALLOW — the blurb carries only the self-case and the triangle, not the corpus's headline negative result

Current blurb:

> "Iterated expectations of your own future judgment, and what they do and do not buy: the
> corpus closes the Total Trust–Value–Tower triangle with direct arrows, and shows
> tower-to-Value fails when questions can reference the selection."

Two gaps (the triangle and selection-menu clauses are grounded in the 2026-08-11 dump —
`projects/deference/note-dump-2026-08-11/README.md` item 3 — and are not contested):

1. "Iterated expectations of **your own** future judgment" describes only the free
   self-instance. The tower `Mart(H→E*)` is the novice's expectation of *an expert's*
   estimate; the self-instance is where it is free (`cee`), and the corpus's central
   question is the **cross-process** tower (`anson-notes/no-timely-pointwise-tower.md` §0;
   `anson-notes/frozen-deliberation-deference-v6.md` §1).
2. The dump's single sharpest theorem is absent: the timely pointwise cross-process tower is
   **unattainable** — on quote-referencing families the Gödel-coin diagonal
   `g_n ↔ (a_n ≤ ½)` forces a defect ≥ ½; on quote-free families the cost-circularity
   regress `R_A(n) ≳ R_A(F(n)) > R_A(n)` makes it underivable; the two cases exhaust all
   families (`anson-notes/no-timely-pointwise-tower.md` §1, §3–§5; kernel-checked per
   `anson-notes/self-referential-settlement-target.md` §10). The tower survives as forced
   only on the timely fragment of the sealed-sibling construction
   (`anson-notes/frozen-deliberation-deference-v6.md` T3, Target-Soundness).

### PROPOSED BLURB

> "Deference as the tower: the novice's estimate of a question equals its estimate of the
> expert's estimate. Free when the expert is your own future self; provably unattainable
> pointwise across two processes — a quote-referencing diagonal misses by ½, quote-free
> families hit the cost-circularity regress — and forced only on the timely-checkable
> fragment of a sealed target. The corpus closes the Total Trust–Value–Tower triangle with
> direct arrows, and shows tower-to-Value fails when questions can reference the selection."

### MISSING LINK: `logical-induction -> deference-tower`

```json
{"from": "logical-induction", "to": "deference-tower", "rel": ["substrate"],
 "why": "the self-instance of the tower is the inductor's free self-trust theorem; across distinct processes it must be earned, and the corpus says exactly where it can be"}
```

Evidence: `anson-notes/no-timely-pointwise-tower.md` §2 ("the self-instance of the tower is
the free logical-induction self-trust theorem cee");
`anson-notes/frozen-deliberation-deference-v6.md` §1 ("for one canonical expert — the
novice's own future self — the tower is free … For a distinct process the tower is handed
over by neither agent's criterion").

### MISSING LINK: `reflection-principles -> deference-tower`

```json
{"from": "reflection-principles", "to": "deference-tower", "rel": ["adjacent"], "undirected": true,
 "why": "the tower is reflection's inductor form and strictly weaker than full Reflection, which conditions on the expert's whole identity and collapses for a modest expert — the ceiling is a feature"}
```

Evidence: `notes/deference-in-logical-induction-v6.md` §1.6 ("It is the tower, not
Reflection … strictly weaker than DDB-Reflection … Reflection collapses to inconsistency for
a modest expert. The ceiling is a feature"); `anson-notes/frozen-deliberation-deference-v6.md`
T5 gloss ("Total Trust is strictly weaker than Reflection (adopting the expert's whole
identity)").

---

## 3. Concept: `total-trust`

### SHALLOW — correct but misses that Total Trust is the *surviving* face and the ceiling

Current blurb:

> "Deference as a decision comparison made precise: trust a process totally when you would
> take its advice on every bet it would change. A finite two-option identity connecting it
> to Value is proved in the corpus."

What the primary material adds: Total Trust is the inequality face that remains available
when the pointwise equality face is impossible, and the gated/averaged form is a **tight
ceiling** for deference to a modest expert — "a theorem about the problem, not a defect of
the proof" (`anson-notes/frozen-deliberation-deference-v6.md` T5;
`anson-notes/no-timely-pointwise-tower.md` §6 "only weaker, non-pointwise notions …
averaged/gated Total Trust … can survive"; `notes/pointwise-tower-and-faithful-acceleration.md`
§4.2).

### PROPOSED BLURB

> "Deference as a decision comparison made precise: trust a process totally when you would
> take its advice on every bet it would change. It is the inequality face of deference —
> equivalent to Value by a tight two-option witness, and in gated, class-averaged form the
> most that can be forced toward a modest expert: the pointwise faces above it are provably
> unattainable across processes."

---

## 4. Wiki page: `wiki/Logical-Induction-and-Deference.md`

### WIKI EDIT A — the page carries none of the note dump's settled mathematics

The page's "What the audits retain" (lines 39–49) records only the corpus-reconciliation
facts (finite identity, soft route, hard-selector failure). The dump's two-sided result —
the line's recorded starting point per `projects/deference/note-dump-2026-06-27/ORIGIN.md` —
appears nowhere on the wiki (verified: no wiki page mentions the tower impossibility,
the anti-inductive diagonal, cost-circularity, frozen deliberation, or faithful
acceleration). Proposed insertion, after the "What the audits retain" section:

> ## What the deference corpus settled
>
> Across two processes the timely, pointwise tower is unattainable: on families that may
> reference the stronger reasoner's quotes, a diagonal contract settling as
> `𝟙[a_n ≤ ½]` leaves every quote off by at least ½; on quote-free families, timely
> tracking of the coupled target would require the stronger class to contain its own
> simulation cost composed with the lookahead. The two cases exhaust all contract families.
> What survives is exact: gated, class-averaged Total Trust — hence classwise Value — is
> forced over all sentences with no appeal to the prior, because the forecaster's
> calibration is settled after the fact against the weaker reasoner's credences, which
> exist for every sentence; and the per-question tower is forced on precisely the
> timely-checkable fragment of a target sealed against the current quote. Forcing is
> co-extensive with settlement: the exploiting trader earns by buy–wait–settle–rebuy, so
> on a question that never settles it acts once, never recovers budget, and freezes. The
> corpus record is
> [`projects/deference/note-dump-2026-06-27`](…/projects/deference/note-dump-2026-06-27)
> (`no-timely-pointwise-tower.md`, `faithful-acceleration.md`,
> `frozen-deliberation-deference-v6.md`), with the obstruction and trader cores
> kernel-checked in its `lean/`.

(Grounding for each clause: `anson-notes/no-timely-pointwise-tower.md` §1, §3–§5;
`notes/faithful-acceleration.md` §4–§5; `anson-notes/frozen-deliberation-deference-v6.md`
T3, T7 gloss ("settlement-powered forcing is co-extensive with settlement and goes silent
the moment settlement is withdrawn (the exploiting trader earns by buy–wait–settle–rebuy;
with nothing to settle it acts once, never recovers, freezes)"); Lean files at
`projects/deference/note-dump-2026-06-27/lean/`.)

### WIKI EDIT B — the third-person disanalogy with DDB belongs beside the DDB section

The page presents DDB's modesty framing ("The motivating decision problem") but omits the
corpus's sharpest departure from it. Proposed two-sentence insertion at the end of that
section:

> The corpus departs from the source in one load-bearing way: Dorst-style deference is
> first-person — the agent expects the expert to be more accurate and therefore defers —
> while the enforced results here are third-person, with settlement arbitrage moving the
> weaker reasoner to the stronger one's estimate whether or not it judges the expert
> superior. On the uplift fragment that judgment is provably unavailable to it, so
> deference that depended on recognizing superiority would fail exactly where the expert is
> superior.

Evidence: `trust-between-inductors-chats/02_2026-06-18_rational-human-trust.md`
L9575–L9581 ("H is forced to defer without being able to recognize A as more trustworthy.
The trust is manufactured by settlement, not inferred by H … you do not have to correctly
judge the stronger system superior in order to be correctly compelled to use it on
checkable questions").

---

## 5. Wiki page: `wiki/Deference.md`

### WIKI EDIT C — ground "Endpoint preservation is ruled out" in the corpus theorem it rests on

Current status passage (lines 147–149):

> "Endpoint preservation is **ruled out** (`DECISIONS.md`, 2026-09-08): legitimate
> influence is causal factorization through declared reasons, not convergence location."

The mathematical ground is in the primary material and stating it makes the ruling
self-supporting for a reader: on never-settling questions the advised reasoner's limit is a
nondegenerate interval the construction does not select from, and the trace cannot tell a
preserved endpoint from a steered one — so convergence location can neither be protected
nor audited, and legitimacy has to be read off the influence path instead. Proposed
replacement sentence:

> Endpoint preservation is **ruled out** (`DECISIONS.md`, 2026-09-08): on questions that
> never settle, the advised reasoner's limit is provably underdetermined and the record
> cannot distinguish a preserved endpoint from a steered one, so legitimate influence is
> causal factorization through declared reasons, not convergence location.

Evidence: `anson-notes/frozen-deliberation-deference-v6.md` T7 ("the achievable values of
`H⁺_∞(P)` for a fixed off-`G` `P` form a nondegenerate interval … The construction selects
no point in it") and the manipulation section ("the trace shows the same vanishing
prediction error whether the AI is faithfully predicting an independent human or predicting
a human it has steered"); `trust-between-inductors-chats/05_2026-06-06_quote-resolution-audit.md`
L11065 ("influence-effectiveness and accountability-destruction are the same operation —
moving the reasoner is erasing where it was").

### WIKI EDIT D — one sentence naming why protection is pre-committed structure

The page's legitimate-deference section describes the committed principal program and
activation machinery without the corpus fact that motivates architecture-over-judgment.
Proposed insertion at the end of the "Deference" paragraph of the active-consumer section
(after "…a sealed commitment is one implementation and is not sufficient alone."):

> The structure is load-bearing because the record alone cannot be: off the checkable
> fragment a captured advisor and a faithful one are indistinguishable from inside, so
> protection has to be a pre-committed policy rather than an in-the-moment judgment.

Evidence: `trust-between-inductors-chats/05_2026-06-06_quote-resolution-audit.md` L11073
("a benevolent A and a captured A are phenomenologically identical on Φ … value-capture has
no warning light by construction, so protection must be a pre-committed policy, not
in-the-moment judgment"); same indistinguishability in
`anson-notes/self-referential-settlement-target.md` §7.

---

## 6. Wiki page: `wiki/What-Deference-Requires.md`

### WIKI EDIT E — "Competence is not calibration" misses the distinction the manipulation program turns on

The section distinguishes competence/calibration/epistemic deference but not the corpus's
sharper split *within* calibration. Proposed insertion after "None supplies authorization or
corrective capability on its own.":

> Calibration itself splits: calibration to the principal's own future credence and
> calibration to truth come apart exactly on questions that never settle, where every
> self-fulfilling equilibrium is perfectly calibrated to the realized credence. An advisor
> can earn its record where truth is checkable and spend the authority where it is not; no
> calibration check on the record separates that from legitimate authority.

Evidence: `trust-between-inductors-chats/06_2026-06-03_note-review-proof-outlines.md`
L3482 ("the single most important piece of missing machinery is a distinction your current
conditions can't see: calibration-to-self vs. calibration-to-truth … Manipulation = A
selecting which self-fulfilling prophecy obtains") and L3486 (the transfer-of-trust attack:
"the certificate was earned honestly on one domain and spent on another");
`trust-between-inductors-summary-v2.md` §6 (manipulation theorem ingredients (a)–(d)).

---

## 7. Cross-cluster link into the normativity cluster

### MISSING LINK: `exclusionary-reasons -> deference-line`

```json
{"from": "exclusionary-reasons", "to": "deference-line", "rel": ["shapes"],
 "why": "Raz's preemption marks the regime switch the corpus formalizes: advice weighed as evidence is bounded by the persuasion martingale — the reflection principle itself — while advice that preempts the recipient's reasons removes the bound"}
```

Evidence: `trust-between-inductors-chats/06_2026-06-03_note-review-proof-outlines.md`
L3484 ("BP's Bayes-plausibility constraint — expected posterior equals prior, a martingale
— is the *same object* as your reflection principle, and it limits how far a strategic A can
move H⁺ in expectation. Preemption removes that bound … the feature that makes authority
real is the feature that enables capture"). The graph has Raz's preemption only as a
normativity-cluster concept; the deference corpus is where it acquires a theorem-shaped
role, and no link records it. (If a single edge must be chosen between this and the
`faithful-acceleration -> legitimacy-line` link of §1, prefer the latter; this one is the
philosophical register of the same boundary.)

---

## NOT ESTABLISHED

Hunches live in the chats that the materials do not settle — questions, not edits:

1. **2b's soft joint.** Whether inexploitability forces the market to pay its simulating
   trader's runtime is explicitly rated ~75–80% and flagged as "the place a rescue might
   live" (`anson-notes/self-referential-settlement-target.md` §3.2, §9). Any blurb or page
   stating the cost-circularity should keep 2a as the airtight half.
2. **Faithful acceleration's deepest residual** — the no-hidden-hard-settlement audit
   (obligation 3, `notes/faithful-acceleration.md` §8): the positive result "lives precisely
   as long as it refuses to build the negative result's diagonal"
   (`notes/pointwise-tower-and-faithful-acceleration.md` §6). Not yet discharged; the
   concept entry should not read as a finished theorem.
3. **Eisenstat's conjecture** — that `A`'s predictions-of-`H` form a logical inductor in
   their own right (`notes/faithful-acceleration.md` §8) — attractive, not needed, not
   proved.
4. **Quote-stability sub-lemma and the patient-to-diagonal lift** — the two named open
   steps on the uplift side of the two-channel forcing theorem
   (`trust-between-inductors-summary-v2.md` §5; chat 02 L9024–L9026). Safety clauses are
   robust to their failure; uplift is not.
5. **Underdetermination for entangled independents** (Con(PA), Gödel sentences): the
   Projection Lemma covers atoms and Boolean combinations only
   (`anson-notes/self-referential-settlement-target.md` §9, chat 09 L5370–L5404).
6. **The manipulation theorem** is a sketch awaiting its four ingredients (second
   calibration condition, evidence/preemption toggle, transfer-of-trust construction,
   non-recoverability) — chat 06 L3490 and summary-v2 §6. The §6 wiki edit above states
   only the parts the chats argue, not the unproved theorem.
7. **Whether the two-inductor idealization says anything about real systems**: the chats
   are explicit that no convergence rates exist anywhere in the framework and that modeling
   humanity as an inductor is itself the strong computability assumption (chat 03
   L3093–L3095; chat 11 L7222–L7280; chat 02 L9640–L9650 "a clean map of a small region").
   This is the `stance-and-level` crux already in the graph; the chats add evidence, not a
   settlement.
8. **Frozen vs. original target as the right alignment model** was left genuinely open in
   the email thread: Anson leaned frozen, Abram found it "more like a hack … I find it hard
   to imagine AI training runs seeking to imitate humans-without-AI-help" and proposed the
   legitimacy modeling instead (`anson-notes/email-thread-note-dump.md`, 21–22 Jun). The
   later workspace design (actual-principal evaluation, no counterfactual evaluator)
   resolves the design choice but the mathematical question — what the frozen construction's
   per-day tower is worth under Abram's two isolation objections — was never answered.
