# Corrigibility cluster — recovered understanding and concrete fixes

Sources read in full: `projects/deference/corrigibility-note-dump-2026-10-01/` (position-statement v1–v3, discussion outline, BLI-thread audit, value-change-as-epistemic-update.md), the clean-room findings files (`corr-position-finds`, `corr-scim-cid`, `lit-mdp-corrigible`, `corr-value-change`), `wiki/Corrigibility.md`, `wiki/Deconfusing-Corrigibility-Companion.md`, `wiki/Value-Change-as-Belief-Change.md`, and the named slice of `state/concepts.json`. All paths below are relative to the repo root. Every item is GROUNDED with the cited path(s).

---

## 1. MISSING LINKS

### 1.1 `value-change-as-belief-change -> total-trust` (rel: uses)

**Why-line:** "the trust grade the decision actually needs: a bounded agent trusts a correction value by value, and the modest source — any retraining process — satisfies Total Trust while failing reflection and superconditioning."

**Evidence:** `projects/deference/corrigibility-note-dump-2026-10-01/value-change-as-epistemic-update.md` §2.7 (the act-value form of Good's theorem; "Total Trust is the trust principle that survives when the state is not a sentence"), §6.6 (Total Trust without (M); "the gap is the modest source, which any retraining process is"), §6.8; `position-statement-v2.md` §1.5 (the author's ruling: "legitimacy can be defined with total trust in the ddb setting. In the LI setting … the translated total trust is equivalent to reflection"). The cluster currently reaches `total-trust` only through the deference line; the corrigibility notes use it as the load-bearing trust principle and the concept graph does not say so.

### 1.2 `value-change-as-belief-change -> reflection-principles` (rel: uses)

**Why-line:** "the licensing rule for a wanted modification is reflection with respect to the modification event; no-expected-net-update alone admits the Dutch-bookable coin."

**Evidence:** note §2.3 ((R⁺) vs (M⁺) and (Z)), §6.3 (the coin satisfies (M) and (Z), fails (R), is Dutch-booked once the outcome is in the agent's algebra, and is strictly worse than no update), §6.8 ("the 2026-09-25 run phrases the legitimacy condition as 'no-expected-net-update with respect to legitimate updates' … this note suggests the phrase should be read as reflection … since only the former distinguishes a teacher from a coin"). `reflection-principles` currently links only into the deference line.

### 1.3 `value-change-as-belief-change -> legitimacy-line` (rel: shapes; cross-cluster)

**Why-line:** "reflection is demanded only conditional on legitimacy, so a correction is learning on the legitimate worlds plus a priced residual pill on the rest — legitimacy detection carries the whole load."

**Evidence:** note §2.3 ("Conditional reflection", AUTHOR 2026-09-30: legitimacy is *not defined* as accuracy improvement; it is the event on which the agent trusts its update process) and §2.6 (the residual pill; the λ > 1/4 base-rate inequality; "legitimacy detection is what keeps the residual pill small"); `position-statement.md` §2.13(b) (the base-rate inequality α/β ≲ (ε/(1−ε))·(h/c)). The wiki page's "Where it sits" already states this hand-over in prose ("which is where legitimacy and the deference corpus's trust relations take over", `wiki/Value-Change-as-Belief-Change.md`); the concept graph has no edge for it.

### 1.4 `dishonest-inner-optimizers -> value-change-as-belief-change` (rel: shapes; cross-cluster)

**Why-line:** "alignment faking read in the thesis: a model shaping its own training data resists its modification ahead of time through the one channel there is, and the resistance is correct exactly when the anticipated modification is illegitimate."

**Evidence:** `position-statement-v3.md` §1.3 (AUTHOR: "There is no special channel, there is just The Channel. … It can only be resisted ahead of time. In the moment, it simply is the moment") and §2 ("The central test case is not the button but a model that shapes its own training data (alignment faking, gradient hacking) … the landscape contains the case where what the control literature calls a corrigibility failure is a correct response to an illegitimate modification"); `corrigibility-discussion-outline.md` A1(c). The `dishonest-inner-optimizers` node currently points only at `authorship-transparency` and `the-program`; the corrigibility materials give it a precise second reading that nothing in the graph records.

### 1.5 `corrigibility-2015 -> value-change-as-belief-change` (rel: shapes, contrast)

**Why-line:** "the paper's three-step model is the thesis's test bed: U_S deleted, the press read as evidence about the value of continuing, desideratum 1 bought by the trust inequality — and the deception case is where unconditional trust breaks."

**Evidence:** `position-statement.md` §2.8 (the model-by-model dictionary: U_S has "no utility counterpart"; "o is evidence about ω"), §2.9 (the Total Trust filler buys desideratum 1 "without any U_S"; it cannot hold for every a₁); the entire `corr-position-finds` package formalizes the position statement on the three-step model (`projects/deference/faf-cleanroom-2026-10-02/packages/corr-position-finds/corr-position-finds-findings.md`, headline and F-1–F-14). The graph currently connects `corrigibility-2015` only to `corrigibility-line` and `anti-natural-corrigibility`; the thesis's closest formal engagement with the paper is invisible.

### 1.6 `logical-induction -> value-change-as-belief-change` (rel: adjacent or substrate)

**Why-line:** "the thesis's hardest test: in LI the translated Total Trust is equivalent to reflection, training pressure enters as pushes through the market, and the learnable part of legitimacy selects for undetectable manipulation."

**Evidence:** `position-statement-v2.md` §1.5 (author's ruling on LI); `corrigibility-bli-thread-and-early-questions-audit.md` §1.3 ("legitimacy detection is a prior, not a theorem"; value-trust is trust by analogy), §1.5 (front-running: "a corrigible agent already believes what it expects to be legitimately taught" becomes the mechanism of fully updated deference; wireheading through the pushers), §1.6 (immune traders, retractions, "the learnable part of legitimacy selects for undetectable manipulation"; the one-unlearnable-constraint proposal).

---

## 2. SHALLOW / WRONG

### 2.1 `corrigibility-line` blurb — one route presented as the line (the flagged error family, mirrored)

**Current blurb** (`state/concepts.json`): "A corrigible agent built from response authority: after any move the agent makes, its principal can still respond and have that response count. The kernel theorem is proved; continuation BRIA is the layer that learns it."

**What the primary material says:** the line contains at least two routes. The kernel route is as stated. The value-change route is the whole note dump: the author's thesis that the anti-naturality arguments have hidden assumptions (`corrigibility-discussion-outline.md`, thesis quoted in full), the general object where "the whole question of corrigibility should be about as broad a space of modifications as it can be, not restricted to some particular shutdown scenario" (`position-statement-v3.md` §1.2), and the broadening where "corrigibility [is] only a subgoal" of the dynamic conditions needed for things to turn out well (`position-statement-v2.md` §1.3, AUTHOR verbatim). The wiki `Value-Change-as-Belief-Change.md` itself describes the landscape as containing "routes, such as the response-authority kernel, that do not rest on it" — plural routes, of which the blurb names one. This is the same error the maintainer flagged for `value-change-as-belief-change` (a route presented as the line), from the other side.

**Proposed blurb:** "The line asks when an agent remains correctable. Its proved route builds the agent from response authority — after any move, the principal can still respond and have that response count — with continuation BRIA as the layer that learns it; beside it, the value-change route examines why correction would be resisted at all, with shutdown one point in a space of modifications."

### 2.2 `value-change-as-belief-change` blurb — the transform claimed to dissolve what it relocates

**Current blurb:** "The thesis under test in the corrigibility notes: represent a change of values as a change of beliefs, and corrigibility stops looking anti-natural."

**What the primary material says:** the note is more precise and more guarded on both halves. (a) The transform's finding is that the simple argument's hidden assumption is "that the modification carries no information about what is valuable. That is a fact about which utility function the agent has, not about expected-utility maximization" (`value-change-as-epistemic-update.md` §0 "The answer, in one paragraph", §4.1: "The question is which utility function the system has, and that is a question about training, not about decision theory"). (b) Corrigibility does not simply "stop looking anti-natural": the information route decays to zero under fully updated deference (§1.5: "as the agent comes to know everything its correctors know, (I) goes to zero — that is the problem of fully updated deference"), what survives is either the payment term (a design fact "which has to be put there and kept there") or legitimacy-conditioned trust with its priced residual pill (§2.6). The problem is relocated to trust in the correction channel, which the wiki page now says; the blurb still says dissolved.

**Proposed blurb:** "Represent a change of values as belief change about a value variable: a trusted correction is then learning, and the anti-naturality argument's hidden assumption surfaces — that the correction carries no information about what is valuable. The transform relocates the problem to trust in the correction channel rather than dissolving it."

### 2.3 Link `value-change-as-belief-change -> continuation-bria`, why "the BLI corrigibility thesis the learning layer carries" — a conflation the materials do not support

**Current why-line:** "the BLI corrigibility thesis the learning layer carries."

**What the primary material says:** in the note dump, "BLI" is the author's name for Sam Eisenstat's belief-structure construction in the logical-induction setting — "'BLI' is the author's name for Sam Eisenstat's construction; nothing about it beyond the author's sentences is in the corpus" (`position-statement-v3.md` §1.3 parenthetical) — and its formal home is the `udt-bli-*` package family (`projects/deference/faf-cleanroom-2026-10-02/packages/`: udt-bli-core, udt-bli-learning, udt-bli-tiling, …). Continuation BRIA is bounded inductive rationality lifted to continuations; `wiki/Continuation-BRIA.md` contains no occurrence of "BLI" and no value-change content (checked by grep). The why-line names an object that belongs to a different thread. Either the edge should be re-grounded without "BLI" (if the learning layer genuinely carries the value-change thesis, nothing read here shows it) or the connection the materials do support should replace it — the thesis's LI-side development runs through the BLI thread and the udt-bli packages, i.e. link 1.6 above, not through continuation BRIA.

**Proposed fix:** drop or re-ground this edge; if an edge from the thesis into the learning layer is wanted, the grounded one is 1.6 (`logical-induction`), with the BLI-thread audit as evidence.

### 2.4 `anti-natural-corrigibility` blurb — states the obstacle without the locus the materials pinned

**Current blurb:** "The standard obstacle: under almost any fixed objective, an expected-utility maximizer resists being corrected or shut down. The argument this line's constructions answer."

**What the primary material says:** the note pins exactly where the argument is valid and where it is ambiguous: "the standard argument is valid for the coarse description, and the coarse description is ambiguous between an agent for which its conclusion is right and an agent for which it is wrong … it is a tautology about an agent whose representation and values have been identified by construction" (`value-change-as-epistemic-update.md` §3.3); the hidden assumption is an utility flat in the correction event. And the once-popular repair of the blurb's register — "every remaining anti-naturality argument is a typical-case claim, none a structural theorem" — was itself corrected at machine-checked strength: wrong for guarantee claims (`corr-position-finds-findings.md` F-9, `not_d1At_of_dominated_on_support`: one every-sensor impossibility theorem in Setting S). "Under almost any fixed objective" is not what the sources establish; what they establish is a conditional.

**Proposed blurb:** "The standard obstacle: by its current utility function, no alternative selects a better act, so a maximizer resists correction unless paid. Valid exactly for an agent whose utility carries no information in the correction event — a fact about which objective the system has, which is where the line's constructions answer it."

---

## 3. WIKI EDITS

### 3.1 `wiki/Corrigibility.md` — no reciprocal pointer to the value-change route

The page is the line's canonical research-state note and is entirely the kernel route; it never mentions the value-change thesis, the anti-naturality examination, or the landscape framing, while `wiki/Value-Change-as-Belief-Change.md` points the other way ("beside routes, such as the response-authority kernel, that do not rest on it"). A reader entering through the canonical page cannot discover the other route exists.

**Proposed insertion**, end of §0 (after "…fully updated deference is dissolved by the typing, not repaired (§5, Box 1)."):

> This page is the response-authority route. The examination of the anti-naturality argument itself — value change as belief change, with shutdown one point in a space of modifications — is on [Value change as belief change](Value-Change-as-Belief-Change) and does not rest on the kernel.

### 3.2 `wiki/Value-Change-as-Belief-Change.md` — the thesis's sharpest consequence for corrigibility is missing

The page's "Where it sits" hands over to legitimacy and the trust relations but omits the note's exact location of fully updated deference, which §4 of the dump's note was explicitly commissioned to draw (the dispatch's "§4's consequences for corrigibility"): the information term vanishes as the agent learns what its correctors know (`value-change-as-epistemic-update.md` §1.5), a predicted correction is under reflection already adopted, and "the residual — corrections predicted and not adopted — are by Claim 1 exactly the ones the agent judges illegitimate" (§7(iii), front-running per the BLI audit §1.5). What persists after nothing is left to learn is the payment term, "a fact about which values the agent has rather than a consequence of its rationality, which has to be put there and kept there" (§1.5).

**Proposed insertion**, in "Where it sits", after the first sentence:

> The transform also locates fully updated deference exactly: the information term vanishes as the agent comes to know what its correctors know, and under reflection a predicted correction is already adopted — the residual, corrections predicted and not adopted, are precisely the ones the agent judges illegitimate (the note's §7(iii)). What persists once nothing is left to learn is the payment term: a fact about which utility the agent has, not a consequence of its rationality (§1.5).

---

## 4. Descriptions checked and found right (no change proposed)

`response-authority`, `corrigibility-kernel`, `deconfusing-corrigibility` blurbs and the `Deconfusing-Corrigibility-Companion` page match their sources; the `instrumental-convergence -> anti-natural-corrigibility` ("the engine of the argument") and `deference-line -> corrigibility-line` why-lines match the materials; the wiki Value-Change page's corrected status line ("one move inside the corrigibility landscape — the base of the `value-change-base-layer` programme") matches the dump.

---

## NOT ESTABLISHED

Hunches the materials do not settle; none is proposed as a link or edit.

- **Whether the two routes meet formally.** The kernel's `Legit` predicate is abstract ("nothing assumed about its content", `wiki/Deconfusing-Corrigibility-Companion.md`, Definitions table), and nothing read shows the note's legitimacy event `L` instantiates it. The hand-over links above are conceptual, not theorems.
- **The legitimacy anchor.** Three candidates are live — accuracy-only, procedural, process-fidelity (implemented = algorithmic output) — and the question is posed to the author and unanswered in the corpus read (`corrigibility-bli-thread-and-early-questions-audit.md` §3 Q1).
- **One unlearnable constraint, or none.** The BLI thread's conclusion (prices of u-sentences invariant to self-caused pushes, as a market constraint) versus the author's "trust can be earned … though the prior should be skewed towards trust" — same object or real disagreement, open (audit §3 Q2; §1.6).
- **Hedged installation.** If a correction process can install the mixture state rather than the L-conditional, the base-rate condition disappears and legitimacy detection stops being load-bearing (note §7(v)). The blurbs above assume the unhedged case, as the note does, but the note marks it a design question.
- **Whether the transform reaches MDP-carrier formalisms at all.** `lit-mdp-corrigible-findings.md` F-19: the MDP state factorisation (Goal × Env) is exactly the distinction the thesis is non-realist about; "no theorem in this package bridges the two, and none could without a different carrier." Any future link asserting the transform covers the Hudson/Nayebi-style formalisms would be wrong on present evidence.
- **The sigma-algebra case.** Value changes outside the convex hull of the prior's support (the opiates/stimulants shape) are deferred by the author (outline item 1 OPEN; note §7(ii)); the cluster's blurbs correctly stay silent on it, and should continue to until it is worked.
