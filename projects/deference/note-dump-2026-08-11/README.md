# Deference in Logical Induction — note dump (2026-08-11)

A working bundle on porting the main theorem of **Dorst, Levinstein, Salow, Husic & Fitelson, "Deference Done Better"** (DDB) — the equivalence **Total Trust ⇔ Value** — into the **logical-induction** (LI) framework of Garrabrant, Benson-Tilsen, Critch, Soares & Taylor, in light of **Weatherson's** "Deference and Infinite Frames" counterexamples — and then carrying the resulting "tower" picture across the gap between **two distinct processes of different computational strength**. The motivating program is **basin-of-attraction / corrigibility** arguments for AI alignment (`notes/li-deference.md`).

This pack **supersedes the 2026-06-27 note dump** and contains everything it did, plus six further weeks of work. *Assembled 2026-08-11 by Abram Demski with Claude, building on and in collaboration with Anson Berns's "Trust Between Logical Inductors" project.*

---

## What's new since the June 27 pack

If you have read the previous pack, this is the delta — roughly in the order it happened. (Registers per the corpus convention: **KERNEL-CHECKED** / **PROVED (prose)** / numbers like ~0.85 are working credences; everything is **unvetted by Abram** unless marked otherwise.)

1. **The faithful-acceleration adjudication** (the "FA chat," July 1–29, `imported-chats/2026-07-01__…a6632d0f.md` + its 44–47 continuation). A long audit of the June FA corpus against the LI paper itself. It found errors in **every** corpus document, found a **printed erratum in the LI paper** (Thms 4.8.15/4.8.16 — real, ~0.95, but not load-bearing: `wiki/li-paper-erratum.md`), retracted and rebuilt the positive result twice (the `notes/fa-positive-*-corrected` files are **mid-chat snapshots** — v1/v2 rest on an architecture retracted at msg 39; v3 is the best file form), and then produced the **delay results**: **Theorem A** (~0.90, the strongest statement in the corpus — on a *fixed* question the accelerator survives arbitrary staleness), **Theorem B** (an impossibility on fresh questions — **since refuted**, instructively), and **Theorem C** (half refuted; the surviving bound ties violations to within-delay update mass). Read `wiki/new-chats-2026-07.md` first — it is the reader's guide to all of this.
2. **The wiki** (`wiki/`, 31 per-result pages + index). The corpus's results of record moved from monolithic notes to per-result pages with explicit status labels (`wiki/conventions-and-status-labels.md`). Where a wiki page and an older note disagree, **the wiki page is the corrected statement** — the supersession table is in `wiki/index.md`. The v6 monolith remains the best single narrative, but several of its claims (e.g. §4.8 "both faces die together", §5.11's Value-failure witness) were corrected in July — the corrections ledger is `wiki/new-chats-2026-07.md` §5 and `imported-chats/analysis/delta-report.md` (D16). (A few wikilink targets, e.g. [[tower-death]] and [[defensible-claims]], are planned pages that do not exist yet — the link marks the intention.)
3. **The deference triangle closed.** Full-menu **Total Trust ⟹ Value** by the keep-or-switch telescope (a proof that existed only in a conversation, now in `imported-chats/2026-07-20__…b9e8341b.md`); the **centered-bet squeeze** making **Total Trust ⟺ Mart timely and cheap** (`notes/centered-bet-squeeze.md`); the **punishing-menu counterexample** showing unconditional argmax Value is false and a scope condition (**conditional-stability**, mass-weighted form) is necessary, not stylistic; the direct **Value ⟹ Tower** argument via gap-bet probe menus; and **Tower ⟹ Total Trust** closing the loop — three direct arrows, with the decision-theoretic assumption charged exactly once. Also: **Mart ⟹ Value refuted**, not merely unproved. See `wiki/total-trust-implies-value.md`, `wiki/value-implies-tower.md`, `wiki/tower-implies-total-trust.md`, and the transcripts.
4. **The varying-question line** (`varying-question-lab/`). Prompted by the question of what the corpus's results say about *Sam Eisenstat's* picture: the lookahead construction (`varying-question-lab/eisenstat-lookahead-construction.md`), **Theorem SS** (~0.82–0.85, kernel-checked engine: scheduled weighted two-sided quote–credence agreement on varying questions under one-way visibility, `varying-question-lab/theorem-ss-streamlined.md`), a route map of four attack lines including a negative construction that **reversed itself under adversarial verification**, and the synthesis (`varying-question-lab/varying-question-synthesis.md`).
5. **The attribution correction (2026-08-11 — the freshest and least-settled material here).** Abram spoke with Sam Eisenstat. The objects the corpus had been calling "Eisenstat's conjecture" are **the corpus's own construal**, which Sam disputes; the celebrated refutation refutes the corpus construal (quote-referencing questions, prompt-ledger publication), **not Sam's intended structure** (delayed quote visibility), which he still expects to be true. `wiki/eisenstat-conjecture-attribution.md` is the correction of record; `wiki/epistemic-discipline.md` is the policy postmortem it produced. The same-day working sessions are in `imported-chats/` (2026-08-11 files) — **entirely unvetted; Sam's views appear only as Abram's same-day paraphrase.**
6. **Legitimacy** (`notes/legitimacy-theory-v1.md` + two claude.ai conversations in `related-chats/`): a first unified sketch — trust, corrigibility, deference, and legitimacy as endpoint-preservation — drawing on the autonomous-lab artifacts below. **CONJECTURE/INTERPRETATION-grade throughout**, explicitly.
7. **The deference-trust lab** (`deference-trust-lab/`): an AI-run exploration lab (scouts → questions → Lean-verified mini-results → red-team → report) over the v2-era corpus. Its findings are inputs to the legitimacy sketch; its ground rules and reports document the method.
8. **Lean growth** (`lean-deference/`): five modules → nine (adds `CenteredSqueeze`, `Staleness`, `StalenessDensity`, `StreamlinedSS` to the June five), all `sorry`-free, all audited to the three standard axioms; `AUDIT.md` remains the statement-level honest account of what the kernel does and does not certify (its per-theorem tables cover the June five in depth; the four newer modules are covered by their result pages' status blocks).
9. **The conversation corpus** (`imported-chats/`, catalogued in its `index.md`): the project now treats working transcripts as **primary sources** — where a transcript and a write-up disagree, the transcript is the authority. Twelve-plus curated transcripts including the origin chat, the FA chat, and the working sessions behind items 3–5; plus chat-authored documents (one of which, `fa-block-staleness-impossibility.md`, exists nowhere else), and analysis briefings (`analysis/delta-report.md` = the FA chronology D1–D19). `related-chats/` adds nine claude.ai conversations from the program's motivation layer (reflection principles, weak-to-strong generalization, bootstrap alignment, DDB close readings, legitimacy).

The June pack's two curated conversations (`transcript.md`, `transcript-v6.md`) and all June materials are retained unchanged (except scrubbing) for provenance.

---

## Where to start

1. **`notes/li-deference.md`** — Abram's human-written motivation. Start here for *why*.
2. **`wiki/index.md`** — the master map and supersession table; then **`wiki/new-chats-2026-07.md`** — the reader's guide to the July corrections (what changed, and which wiki page each insight became).
3. **`wiki/eisenstat-conjecture-attribution.md`** — the freshest correction: what the negative results do and do not refute, and whose conjecture is whose. Read before quoting any "X is dead" claim from this pack.
4. **`notes/deference-in-logical-induction-v6.md`** — still the best single narrative (the tower, the negative result, the two positive constructions, the Vetting Ledger in Appendix B) — read *with* the wiki corrections in mind. **`notes/pointwise-tower-and-faithful-acceleration.md`** — the explainer for how the negative and positive results are two faces of one object.
5. **`imported-chats/index.md`** — the primary-source corpus and how to cite it (chat + message number).
6. **`lean-deference/AUDIT.md`** — read before trusting any "kernel-checked."
7. **`anson-notes/`** — the parallel "Trust Between Logical Inductors" project (Anson Berns, with Demski): summary, construction notes, source conversations.

---

## Contents

```
README.md              ← you are here
transcript.md          ← the v5-era working conversation (curated, June pack)
transcript-v6.md       ← the v6-era working conversation (curated, June pack)

notes/                 ← the note lineage and standalone results
  li-deference.md                              ← MOTIVATION (human-written) + the program's open problems
  deference-in-logical-induction-v6.md         ← LEAD narrative + Vetting Ledger (v1–v5 kept for provenance)
  pointwise-tower-and-faithful-acceleration.md ← EXPLAINER: negative & positive as two faces of one object
  faithful-acceleration.md / -scope.md         ← the June positive + its scope-decision note
  fa-positive-result-corrected.md / -v2 / -v3  ← ⚠ mid-chat snapshots; v1/v2 rest on a retracted architecture
  centered-bet-squeeze.md                      ← Total Trust ⟺ Mart, timely and cheap (July)
  delay-program.md                             ← the delay-results program: what is proved, what to prove next
  legitimacy-theory-v1.md                      ← the legitimacy unification sketch (conjecture-grade)
  roadmap.md                                   ← the long-arc research vision (stages 1–6)
  deference-in-logical-induction-check.py      ← sympy sanity-checks

wiki/                  ← RESULTS OF RECORD: 31 per-result pages + index; status labels per
                         conventions-and-status-labels.md; start at index.md / new-chats-2026-07.md
                         (cross-references use [[wikilink]] names: [[foo]] means wiki/foo.md)

imported-chats/        ← PRIMARY SOURCES: curated conversation transcripts (claude.ai + Claude Code),
                         chat-authored documents, analysis briefings; catalogued in index.md
related-chats/         ← nine claude.ai conversations from the motivation layer (see its README.md)

varying-question-lab/  ← the Eisenstat-picture line: lookahead construction, Theorem SS, route notes, synthesis
deference-trust-lab/   ← the AI-run exploration lab: agenda, scope, runs, red-team, findings, report

lean-deference/        ← kernel-checked: Lean 4 + Mathlib, nine modules, all sorry-free, audited to the
                         three standard axioms; AUDIT.md is the honest statement-level account
  LeanDeference.lean  SelfReferentialTarget.lean  FrozenDeliberation.lean  FaithfulAcceleration.lean
  TowerAndAcceleration.lean  CenteredSqueeze.lean  Staleness.lean  StalenessDensity.lean  StreamlinedSS.lean
  AUDIT.md  lakefile.toml  lake-manifest.json  lean-toolchain

anson-notes/           ← the "Trust Between Logical Inductors" project (Anson Berns, with Demski):
                         summary-v2, the obstruction + construction notes, INDEX over the source
                         conversations, the 11 raw conversations, the June email-thread note dump,
                         and the dose-response Lean note-dump (2026-07-02)

references/            ← THIRD-PARTY sources (see note below): DDB (PDF + transcription),
                         Weatherson (PDF + transcription), the LI paper (compilable LaTeX source),
                         and "Boundedly Rational Deference" (a talk deck cited by notes/delay-program.md)
```

---

## What is and isn't established

The honest accounting lives in three places: **`lean-deference/AUDIT.md`** (statement-level: the kernel proves the deference *algebra and composition*; the LI-paper theorems and the market itself enter as named, trusted hypotheses — "kernel-checked" never means the *forcing* is machine-proved), the **Vetting Ledger** (v6 Appendix B), and **`wiki/conventions-and-status-labels.md`** (the status vocabulary every wiki page carries). Three standing warnings:

- **Mid-chat snapshots.** `notes/fa-positive-result-corrected.md` and `-v2` are actively misleading if read alone (architecture retracted at FA-chat msg 39); v3 is best but predates the delay results. The transcript is the authority; the wiki pages carry the corrected statements.
- **Attribution.** Several results were developed under a construal of Sam Eisenstat's conjecture that Sam disputes. `wiki/eisenstat-conjecture-attribution.md` re-labels the verdicts; claims of the form "X's conjecture is false" should not be repeated from older pages.
- **Vetting.** Almost everything from July onward is **unvetted by Abram** unless a page or message says otherwise; the corpus convention is to say so on the page. The 2026-08-11 material is same-day fresh.

This bundle is **working research**, not a finished paper — including, deliberately, its record of retractions, reversals, and corrections; the project treats those as content, not embarrassment (`wiki/epistemic-discipline.md`).

---

## Building the Lean (optional)

Checked against **Lean 4.27.0 + a matching Mathlib**. Drop `lean-deference/` into a fresh Lake project and build (it fetches Mathlib per `lakefile.toml` / `lake-manifest.json`; fetch prebuilt oleans first to avoid a from-scratch Mathlib build). Build artifacts and the Mathlib checkout are deliberately not shipped. Most modules end with `#print axioms …` lines, so a green build re-prints the axiom audit (`CenteredSqueeze.lean` currently lacks them — run `#print axioms` on its theorems by hand).

---

## A note on `references/` and transcripts

Third-party papers are included as a convenience so the notes are self-contained: **Dorst–Levinstein–Salow–Husic–Fitelson**, "Deference Done Better" (*Philosophical Perspectives* 35, 2021; PDF + transcription); **Weatherson**, "Deference and Infinite Frames" (*Australasian Journal of Logic*, 2025; PDF + transcription); **Garrabrant et al.**, "Logical Induction" (2016, arXiv:1609.03543; compilable LaTeX source). Please **cite and rely on the published originals**. "A Decision-Theoretic Approach for Managing Misalignment" (Herrmann, Chari, Qian, Sharvesh & Levinstein) is discussed in the conversations but not reproduced. `Boundedly Rational Deference.pdf` is a talk deck the delay-program note cites as "the deck."

**Transcript provenance.** Conversation transcripts are curated **substance-only**: tool-call bodies, session logistics, and computing-infrastructure asides are removed, with message numbering preserved (gaps mark omissions, each file's provenance appendix says what was omitted and why); the mathematics is verbatim. The one exception is `anson-notes/trust-between-inductors-chats/` — those 11 conversations ship **raw, as received**, tool-call blocks and all. The corpus citation convention is **chat uuid + message number** (e.g. "chat `a6632d0f` msgs 42–43"), which the numbering-with-gaps preserves.
