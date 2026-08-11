# Eisenstat's conjecture: attribution and setup correction

*A naming and attribution correction, recorded 2026-08-10 after Abram spoke with Sam Eisenstat about the state of his conjecture. The objects this corpus has been calling "Eisenstat's conjecture", "Sam's conjecture", "the Eisenstat merge", and "Eisenstat's lookahead construction" are formalizations whose information structure does **not** match what Sam intended, and the corpus's negative verdicts on those formalizations are **not** verdicts on his conjecture. Every page that uses those names should be read through this one. Written by Claude from Abram's account; the analysis in §4–§5 is unvetted by Sam. Conventions: [[conventions-and-status-labels]]. Master map: [[index]].*

---

## 1. The conjecture as originally recorded

Abram's two contemporaneous, human-written records (quoted, not paraphrased):

From `li-deference.md` §0.3:

> Imagine a model with a "slow but trusted" logical inductor $H$, representing idealized human scientific and philosophical progress, and a "fast but untrusted" inductor $A$, representing a potentially misaligned AI. Is there some way to construct a combined "fast and trusted" inductor? In one discussion about this, Sam Eisenstat conjectured that such a thing could be constructed by looking only at $A_n$'s beliefs about $H_{f(n)}$, where $f(n)$ is some speedup function. $A$'s beliefs about $H$ should converge to the same limit as $H$ does, which is a good start. Would they also be a logical inductor (satisfy the logical induction criterion)? Would they be trusted by $H$?

From `deference-trust-lab/AGENDA.md` ("Fast Student, Slow Teacher"):

> Sam's conjecture: if the AI has good feedback about the human beliefs, and if $f$ grows fast enough, then $B_t$ will itself be a logical inductor, and furthermore, its beliefs will be endorsed by $H_t$ (in the weak sense that makes sense in a logical induction context).

So the object is the **lookahead expectation** $\mathbb E^\ast_n(\cdot) := \mathbb E^A_n\big(\ulcorner \mathbb P^H_{f(n)}(\cdot)\urcorner\big)$, and the conjecture has an **inductor half** ($\mathbb E^\ast$ satisfies the criterion) and a **trust half** ($H$ endorses $\mathbb E^\ast$, LI-weak sense).

Abram's direct clarifications (2026-08-11, in-repo chat):

- the two closing questions of the li-deference record **are** the conjecture (he may edit that file for clarity — it is his; AIs don't modify it);
- **both halves are part of the conjecture**, with the **trust half the more important**;
- **limit-agreement is *not* part of the conjecture** — it is an easy lemma given adequate feedback (an earlier version of this paragraph listed it as a third component; corrected);
- **notation**: abbreviate the lookahead expectation as $\mathbb E^\ast_n$, as in li-deference's own Formalism section — **not** $B_n$/$B_t$ (AGENDA's notation) — so it keeps looking like an expectation. Pages predating 2026-08-11 use $B_n$; read them through this line (also recorded in [[conventions-and-status-labels]]).

## 2. Sam's clarification (2026-08-10, as relayed by Abram)

Sam quite strongly holds that the **strong student / weak teacher** framing Abram was using in the conversation where the conjecture was made (the corpus's "fast student / slow teacher" label names the same framing) implies a specific information structure:

- **the AI (the strong student) knows the human's beliefs immediately**; and
- **the humans learn the AI's beliefs only at a delay.**

Details Abram is **not certain** Sam would endorse — this uncertainty is deliberate and is itself the documented position:

- whether the human-side delay is a **fixed computable function** or only **eventual** knowledge (the humans learn the AI's beliefs eventually, with no schedule);
- consequently, how the delay relates to the lookahead $f$ — in particular whether the human's deliberation at day $f(n)$ has, or has not, absorbed the AI's day-$n$ quote by the time it serves as the forecast target;
- what further conditions (a "good feedback" clause, the class gap $\mathcal C_H \subsetneq \mathcal C_A$, same vs. different theories) belong to the intended statement.

Sam continues to expect the conjecture, **as he intended it, to be probably true**. Nothing in this corpus refutes it (§4).

**Abram's own position, now distinct (2026-08-11, direct).** Abram was surprised by Sam's insistence. He considers the *reversed* structure — the humans knowing the AI's beliefs immediately — the slightly more realistic-to-live version, and holds that the fast-student/slow-teacher content is better captured by the **trader-class complexity gap** $\mathcal C_H \subsetneq \mathcal C_A$ (capability) than by any visibility asymmetry. Consequence for reading this page: there are now **two named versions**, both live research targets — **Sam's version** (AI reads $H$ immediately; humans delayed) and **Abram's version** (humans read the AI immediately; the AI has slow/feedback-grade access to $H$). The corpus's construals (§3) approximate *Abram's* version — nearest existing formalization: the one-way setting of [[eisenstat-lookahead-construction]] — so the corpus is a body of results about Abram's version that was misfiled under Sam's name: the error was in the *naming*, not in the choice of object to study.

**The computability fork (Abram, 2026-08-11) — a formalization axis both versions must declare.** Is the human inductor **computable**, hence in-principle perfectly simulable by a strong enough $A$? Argument for: an AI going through RSI eventually predicts physics very well, and humans are made of physics. In Abram's slow-feedback version, computable-$H$ asymptotically *undoes* the slow feedback — the AI can eventually learn to model the humans perfectly and faster, so the humans hold no permanent epistemic advantage over the AI. Without the assumption, the humans could always know things the AI doesn't, which should significantly weaken the result. Abram reads Sam's immediate-knowledge assumption as doing a similar job by a different mechanism (visibility rather than capability). Note: the corpus already sits silently on the computable branch — its settings assume $A$ can simulate $H$ to the lookahead and its targets are $\Gamma_A$-determined ([[setting-and-notation]]); the uncomputable-$H$ branch is unexplored everywhere in this corpus.

**Sam's further expectations (via Abram, 2026-08-11).** (i) The positive argument should be **fairly simple, and at trader level** — a trader exploits the human market by trusting the AI, because the AI is in fact a good predictor of future human market prices — rather than assembled from LI paper theorems. The corpus's closest existing object is the realized-cash round-trip trader (`varying-question-lab/route-recurring-ccee.md` Thm 5.2: buy the question at day $i$ at $\mathbb E^H_i(X_i)$, unwind at day $f(i)$), whose weighting sparsity is *forced by risk budget* (Prop. 5.3: bounded open-position risk ⟺ $f$-patience ⟹ weight mass $O(\log^\ast n)$) — the current, possibly-not-final account of why the simple argument has not yet delivered the per-day grade under one-way visibility. (ii) Sam locates the *definition* of trust in **accuracy** — a further DDB equivalence never translated to the LI setting; [[deference-notions]] has no accuracy entry. Filed as open work, deliberately not attempted 2026-08-11 (Abram's instruction); Sam expects the argument formalizable relative to tower / Total Trust regardless.

## 3. What the corpus formalized instead

Between 2026-05 and 2026-08 the corpus attached Sam's name to several distinct formalizations. Their information structures, set against Sam's two bullets:

| corpus setting | AI's view of the human | human's view of the AI | matches Sam's stated intent? |
|---|---|---|---|
| deference-trust-lab merge thread (Q4, 2026-06) | "good feedback" hypothesis — weighting-relative, timeliness-bounded | side-discussion ((L)-like publication) | partially — feedback hypothesis, not immediate knowledge |
| tower-death setting (`anson-notes/no-timely-pointwise-tower.md`; deference-v6 §4) | records realized prices (feedback only) | **reads the quote ledger by stage $n+1$ — immediate** | **no** — the delay sits on the wrong side |
| v3 / joint clearing ([[joint-clearing-and-trader-class]]) | live, same-round | live, same-round | half — AI side yes, but no human-side delay |
| one-way visibility (Setting 2 one-way; [[eisenstat-lookahead-construction]], Theorem SS) | **never reads $H$'s prices** | reads the published ledger same-day | **no — both directions reversed** |
| delay/freeze program (BSI; [[delay-and-visibility]]) | **frozen/delayed** | reads ledger | **no** — delay on the wrong side |
| frozen-deliberation construction (deference-v6 §5.1–5.8) | simulates the sealed sibling | settlement copy sealed from $A$ entirely | closest on the human side (settlement copy's delay is effectively infinite) |

Abram's own original formalism (`li-deference.md` §Formalism) is the nearest recorded structure to Sam's bullets: it has a **publication function** $e(n)$ with $n < e(n) < F(n)$ — the humans see the AI's day-$n$ answers only at day $e(n)$, a genuine human-side delay. The downstream corpus quietly dropped that delay (immediate ledgers, same-day sequential clearing) and explored delays on the AI side instead — which is where the drift happened. Note even the original formalism fixes publication-before-lookahead ($e(n) < F(n)$), which is one of the unpinned details of §2.

A second, smaller drift: the referent of the name wanders within the corpus. Most pages use "Eisenstat's merge conjecture" for both halves; `faithful-acceleration.md` L213 uses "Eisenstat's conjecture" for the **inductor half only**.

## 4. What was actually shown, and what it does and does not say about Sam's conjecture

The corpus's theorems stand as theorems **about their declared settings**. What changes is what they may be said to be *about*. Ledger of the main verdicts, each with its register:

1. **REFUTED in-setting, by explicit counterexample:** the timely pointwise tower — for all e.d. $X_n$, $\mathbb E^H_n(X_n) \approx_n \mathbb E^H_n\big(\ulcorner \mathbb E^A_n(\ulcorner \mathbb E^{H^+}_{F(n)}(X_n)\urcorner)\urcorner\big)$ — in the mutual-legibility setting with prompt ledger publication, on question families that may reference the AI's quote. The Gödel-coin diagonal $g_n \leftrightarrow (a_n \le \tfrac12)$ forces a defect $\ge \tfrac12$ (`anson-notes/no-timely-pointwise-tower.md` 2a; deference-v6 §4.3/§4.8; arithmetic core kernel-checked). Via the loop ([[total-trust-implies-mart]], [[value-implies-tower]]), full-strength cross-process Total Trust over quote-referencing-closed classes dies with it — the "paradox route". **Scope, per the source pages themselves:** the counterexample *requires* (i) quote-referencing questions, and (ii) the human's process holding the day-$n$ quote as decided data in time (immediate ledger; more generally publication before the lookahead). It is a refutation of the corpus construal, not of Sam's structure, in which the human-side view of the quote is delayed and (ii) may simply fail — [[weak-loop-and-value-transport]] §3.3 already localizes the refutation to the "quotes are decided data for $H$" regime, and notes it dissolves under the joint fixed point; delayed publication past the lookahead is a second regime in which the diagonal cannot be run as written *(this last inference: Claude, 2026-08-10, unvetted)*.
2. **UNDERIVABLE-not-refuted, in-setting:** on quote-free families, the same pointwise tower is not refuted but its only known proof route needs an unsatisfiable power assumption (2b cost-circularity; the cost-accounting soft joint is itself only ~0.75–0.8). Note the regress runs through the human's deliberation *having absorbed the AI's quotes*; a settlement target sealed past the lookahead is "reflectively blind", and blindness is exactly the regime where the corpus **forces** the tower positively (deference-v6 §4.4, §5) — so under a long enough human-side delay the corpus's own machinery pushes toward the *positive* branch, not the negative one *(Claude's reading, unvetted)*.
3. **PROVED TRUE, weaker grades (in their settings):** Half 1 honesty (unconditional; engine kernel-checked); Lemma P; Theorem A — on a fixed question the accelerator works under arbitrary delay *of the AI's view of the human* with no visibility in either direction, ~0.90, with a two-sided per-day upgrade; Theorem SS — scheduled weighted two-sided quote–credence agreement on varying questions under one-way visibility, ~0.82–0.85; the frozen-deliberation construction forces the per-day tower on the timely fragment $G$. See [[faithful-acceleration-result]], [[eisenstat-lookahead-construction]], [[delay-and-visibility]].
4. **OPEN, with failed refutation attempts:** per-day varying-question trust under one-way visibility — two impossibility constructions died (BSI refuted 2026-07-29; the introspective redesign self-reversed 2026-07-30), and the surviving tools point weakly toward "true" (~0.2–0.3 that a counterexample exists). See [[delay-and-visibility]] §3, `varying-question-lab/route-negative-introspective.md`.
5. **UNTOUCHED:** the inductor half — zero cases discharged, no proof and no refutation, in any setting (deference-v6 §8 D3). The lab's "no-feedback hole" (`deference-trust-lab/findings/merging-inductors-ideate.md` Idea 1) is a CONJECTURE-level argument that the *unconditional* form fails in the lab's feedback-hypothesis setting; its own honest conclusion was the conditional form ("inductor-like on the good-feedback subsequence, unconstrained off it").
6. **Never evaluated:** the conjecture in Sam's stated structure — AI-side immediate knowledge of $H$, human-side delay, with the delay's form unpinned per §2. No corpus setting instantiates it (§3), so no corpus verdict transfers to it without new work. AI-side-immediate visibility is *stronger* than what the positive results need on that side (Theorem A needs none), but the human-side channels the positive results use (same-day ledger, (L)) are stronger than Sam's delayed human, so the positive results do not automatically transfer either.

**The one-sentence summary owed to Sam:** what was refuted, rigorously, is a *pointwise-equality* trust property for a construal in which the humans see the AI's quotes immediately and the questions may reference those quotes; the averaged/scheduled trust properties were largely *proved* in adjacent construals, attempted impossibilities for them kept dying, the inductor half was never touched, and the conjecture under his intended information structure has not been formalized, let alone refuted.

## 5. Naming policy (from 2026-08-10)

- **"Eisenstat's conjecture" / "Sam's conjecture", unqualified, refers to Sam's conjecture as he intends it** — information structure per §2, remaining details unpinned per §2 — status **OPEN** (Sam: probably true).
- The corpus's formal objects should be named by their settings: **"the lookahead construction (corpus construal)"**, "the merge under joint clearing", "the one-way lookahead setting", "the frozen/sealed-sibling target", etc. Where an existing page says "Eisenstat's merge conjecture" or similar, read it as the corpus construal.
- **Formalizing Sam's intended structure is filed as open work**: a publication schedule $e(n)$ on the human side (or an eventual-knowledge variant), AI-side immediate reading of $H$'s prices, and a re-run of both halves of the conjecture there — including whether the diagonal can be rebuilt at all when $e(n) > f(n)$, and what the timing $e(n) \lessgtr f(n)$ does to the trust half (cf. the nesting/timing prediction at [[varying-question-synthesis]] §5 and `route-transitivity`). The **computability fork** (§2) is a further axis any formalization must declare; the **accuracy notion** of trust is a missing menu item at [[deference-notions]].
- **Vetting infrastructure (2026-08-11):** Anson Berns's Lean 4 + Mathlib formalization of the LI paper (`github.com/A-M-Berns/Formalized-Agent-Foundations`, `LogicalInduction/`) is in a usable state per Abram — the repo reports all 53 named theorems/lemmas formalized (51 at paper strength, 2 qualified; zero `sorry`/`axiom` beyond one upstream Foundation gap; fuel-clocked efficiency model). Future verdicts on any version of the conjecture should prefer discharge against it — formalizing in LI directly — over the corpus's existing mode (Lean-checking analytic engines with LI theorems assumed; see honesty caveat in [[conventions-and-status-labels]]). One check before relying on it for Setting-2 work: the corpus's class-gap machinery ($\mathcal C_H \subsetneq \mathcal C_A$) goes beyond the paper's single-class criterion, and the fuel-clock efficiency model's fitness for that generalization is unverified.
- **Historical documents are left as written** (imported chats, `anson-notes/trust-between-inductors-chats/`, lab archives, superseded FA files): their usage is read through this page rather than edited.

## 6. Where corrections were applied (2026-08-10)

Dated attribution notes pointing here were added to: [[eisenstat-lookahead-construction]], [[varying-question-synthesis]] §6, [[faithful-acceleration-result]], [[weak-loop-and-value-transport]], `delay-program.md`, `faithful-acceleration.md` §8, `legitimacy-theory-v1.md`, `deference-in-logical-induction-v6.md` §8 (D3), `anson-notes/no-timely-pointwise-tower.md`, and the deference-trust-lab entry points (`findings/00-orientation.md` Q4, `findings/merging-inductors-ideate.md`, `models/merging-inductors-model.md`, `report/RESEARCH-REPORT.md`). `li-deference.md` and `AGENDA.md` are Abram's human-written files and were not modified; their recorded statements are quoted in §1 and are the closest things in the corpus to the intended conjecture.

## Related

- [[epistemic-discipline]] — the process postmortem of this failure, and the policy adopted from it (2026-08-11)
- [[eisenstat-lookahead-construction]] — the corpus construal's claim ledger (one-way setting)
- [[faithful-acceleration-result]] — the trust-half positive results and their three routes
- [[delay-and-visibility]] — the visibility/delay axes; the refuted impossibility
- [[weak-loop-and-value-transport]] — §3.3, the sequential-vs-joint discontinuity that localizes the tower refutation
- [[joint-clearing-and-trader-class]] — what mutual same-round visibility costs
- [[setting-and-notation]] — the two settings as the corpus defined them
- [[open-problems]] — where the formalize-Sam's-structure task should be tracked
- [[tower-death]] (planned page) — the in-setting refutation; live home: `anson-notes/no-timely-pointwise-tower.md`
