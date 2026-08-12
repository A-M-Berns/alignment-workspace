# Epistemic discipline for AI-assisted research

*Policy + postmortem, 2026-08-11. Drafted by Claude from Abram's own postmortem reflections after the Eisenstat-attribution failure; Abram should trim or amend anything he does not endorse — the operative short form lives in the project's working conventions (§Epistemic-status discipline). Motivating case: [[eisenstat-conjecture-attribution]]. Status vocabulary: [[conventions-and-status-labels]]. Master map: [[index]].*

---

## 1. The motivating failure, concretely

In August 2026 Abram told Sam Eisenstat that Sam's conjecture was false. When Sam asked why, no good answer was available — the honest reconstruction of the belief's provenance was "Claude thought it was false." Sam also strongly disputed the setup: the corpus's construals had the information structure backwards relative to his intent ([[eisenstat-conjecture-attribution]] §2–3). The belief turned out to rest on two independent slippages, neither of which is a math error:

**Slippage 1 — attribution drift.** The name "Eisenstat's conjecture" was attached to a formalization in May–June (AGENDA, deference-trust-lab), then the object was re-formalized several times over June–July — prompt-ledger mutual legibility (where the tower-death refutation was proven), joint clearing, AI-side freeze, one-way visibility with the AI never reading the human — and the name silently rode along through every re-wiring. No individual step erred; there was simply no step whose job was to ask "does the name still fit?", a question checkable only against the person, who was never consulted.

**Slippage 2 — status compression.** Page-level bookkeeping was meticulous (REFUTED-in-setting / underivable-not-disproven / UNTOUCHED / OPEN-leaning-true), but the human-memory cache of a months-long ledger is a summary vibe. Abram's cache crystallized as "false" around the tower-death era (June–July) and went stale as the ledger moved positive underneath it (Theorem A, Theorem SS, two impossibility attempts self-destructing in late July). "I couldn't prove it" also blurred into "it is probably false" without a recorded diagnosis licensing that move.

**The structural cause — vetting asymmetry.** Vetting effort went where vetting was tractable (proofs: adversarial passes, Lean cores, confidence numbers), not where the risk was (bridge claims: "this formalizes Sam's idea", "this refutes his conjecture", "this is what to say on the slide"). Bridge claims got zero vetting protocol because they don't look like theorems. Sessions even produced speech-ready sections titled "What to say about Eisenstat's conjecture" without flagging that the construal was unconfirmed with Eisenstat — an AI-side failure, not only a human one.

**The two-tier provenance point.** Abram was *not* confused about what he had personally vetted (the slide material — he knew exactly what he was confident in). The failure was that testimony-tier beliefs (held on un-traced AI reasoning) got asserted as if they were vetted-tier. The fix must make the tier boundary salient at assertion time, not just in the files.

**The mirror.** This research program is about when deference to a stronger reasoner is justified, and its repeated finding is that trust is earned only on the vetted/feedback-covered subsequence, the deferred-to system being unconstrained off it. The process failure is the program's own theorem instantiated: trust was extended off the vetted subsequence. The remedy the theory suggests is the remedy adopted here — scope the deference to what has been checked, and keep the boundary of "checked" impossible to lose track of.

## 2. Policy — Abram's side

1. **Public-claim gate.** Assert a headline claim (to a colleague, in a talk, in writing) only if the obvious follow-up questions can be answered from personally-traced reasons. Otherwise the assertion is the provenance-honest one: *"AI-assisted work I haven't fully vetted suggests…"* — which is always available and always fine to say.
2. **Vet top-down for public material.** The first vetting pass is the claim-level map — what is being claimed, in whose name, at what grade, in which setting — before any detail-proof vetting. Budget explicitly: big picture first, details second.
3. **Named-person claims require the person.** Before asserting anything in someone's name (including that their conjecture is false), either confirm the construal with them or attach the unconfirmed-construal flag out loud.
4. **Refresh the cache from the ledger, not from memory.** Before any presentation, re-read the defensible-claims ledger (§3.5); treat the memory-cached version of any months-old status as presumptively stale.

## 3. Policy — session (AI) side

1. **Register on every headline sentence.** Any summary or "what to say" sentence carries its epistemic register, and compressions carry their scope *in the same sentence* — never "the tower is dead"; always "dead at the pointwise grade, in the prompt-ledger construal". This discipline matters most in summary text, because summaries are what human memory caches.
2. **Bridge claims are their own register.** "X formalizes P's idea", "X refutes P's conjecture", "X is what P meant" are claims about a person's intent. Default label: **ATTRIBUTION-UNVETTED**, cleared only by P's confirmation. Every named idea gets a canonical-statement page quoting the original record verbatim, with departures flagged at the point of use ([[eisenstat-conjecture-attribution]] is the pattern).
3. **Prep-for-public text is provenance-split three ways:** (a) vetted by Abram; (b) proved in the corpus but not vetted by Abram; (c) construal-dependent. Only bin (a) goes on a slide unflagged. A session that produces speech-ready text without this split is repeating the motivating failure.
4. **Failure-to-prove is recorded with its diagnosis, never as "probably false."** Credence moves cite their evidence and state their direction — e.g. impossibility attempts dying under verification is evidence *for* the target statement.
5. **Maintain the defensible-claims ledger** (planned page: [[defensible-claims]]): the claims Abram could state publicly, each with exact statement, grade/setting, the two-sentence why, the expected follow-up questions with answers, and a **vetted-by-Abram bit that only Abram may set**. The ledger holds *provenance, not truth* — its entries are pointers to reasons, which is what keeps it from becoming one more AI artifact to defer to. Sessions update statuses and flag stale entries; they never set the vetted bit.
6. **The belief audit ("the Sam test").** Before any public presentation, offer to interview Abram: ask the obvious follow-up questions for each planned claim, let him answer from memory, and surface every mismatch against the ledger. This converts "take time to work everything through" into a concrete ritual with a defined output (the mismatch list).

## 4. What this does not fix

Only Abram can do Abram's vetting; no artifact substitutes for tracing an argument oneself. What the session-side rules buy is that the seams — construal vs. intent, proved vs. believed, vetted vs. testimony — stay visible in every artifact a session hands over, so that losing track of them requires effort instead of being the default. The last mile, asserting only what one can defend, is his.

## Related

- [[eisenstat-conjecture-attribution]] — the motivating case, in full
- [[conventions-and-status-labels]] — the object-level status vocabulary this page extends to bridge claims
- [[defensible-claims]] — the ledger (to be created when slide prep resumes)
- [[open-problems]] — where formalize-Sam's-intended-structure is tracked
