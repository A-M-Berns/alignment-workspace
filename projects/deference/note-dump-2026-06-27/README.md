# Deference in Logical Induction — note dump (v6)

A working bundle on porting the main theorem of **Dorst, Levinstein, Salow, Husic & Fitelson,
"Deference Done Better"** (DDB) — the equivalence **Total Trust ⇔ Value** — into the
**logical-induction** (LI) framework of Garrabrant, Benson-Tilsen, Critch, Soares & Taylor, in
light of **Weatherson's** "Deference and Infinite Frames" counterexamples — and then carrying the
resulting "tower" picture across the gap between **two distinct processes of different
computational strength**, where it meets a sharp **negative result** and **two** matching
**positive constructions**.

It contains the research notes (the human-written motivation; the lead **v6** note and its v1–v5
provenance; the positive *faithful-acceleration* note and the *no-timely-pointwise-tower* negative
note; an explainer fitting the two together; a scope-resolution note; and a Python sanity-check), a
kernel-checked Lean 4 formalization **with a statement-level audit of what it really proves**, the
Anson Berns collaboration materials (a distilled technical summary, two construction notes, an index
over the source conversations, the raw conversations, and the email thread that shared the bundle),
the two conversations behind the work (a v5-era and a v6-era transcript, scrubbed), and the source
papers it all builds on.

*Assembled 2026-06-27 by Abram Demski with Claude (Opus 4.8).*

---

## The one-paragraph result

Deference between two epistemic processes — a **novice** logical inductor `H` and an **observable,
coherent expert** `E*` — **is the tower / universal-martingale property**, call it **Mart**:

```
    E^H_n(X)  ≈ₙ  E^H_n( ⌜E*(X)⌝ )      for every efficiently-computable LUV X.
```

and **`Value ⟺ Mart`** for any such expert (the LI analog of DDB's Theorem 2.2), both directions
cheap. The subject is **when the tower can be *forced***: it is *free* for the novice's own future
self (`E* = H_{f(n)}`, where Mart is an LI theorem) and **impossible in general** across two
processes. Across processes there is then **one sharp negative result and two positive
constructions**:

- **Negative.** The **timely, *pointwise* tower** — `H`'s credence today equalling its estimate of
  `A`'s quote, question by question — **cannot be forced**. On a quote-referencing diagonal it dies
  by an explicit anti-inductive (Gödel-coin) counterexample, and **both faces die together** there:
  the tower *and* averaged calibration. (v6 sharpens v5's "tracking" statement to the tower itself.)
- **Positive 1 (timely fragment).** With a blind, **held-out "sealed sibling"** target, the
  cross-process tower is forced — faithfulness everywhere, soundness exactly on the **timely
  fragment** `G`.
- **Positive 2 (faithful acceleration).** With `A` forecasting `H`'s **own future credences**, `H`
  is forced into **gated/classwise Value** — a *faithful accelerator* relaying the human's considered
  judgment sooner — over an **admissible domain** rather than only the timely fragment. The admissible
  domain *cannot* be a clean syntactic fragment (PA rebuilds the quote-referencing diagonal by
  Gödel's lemma), so admissibility is a **causal/provenance** condition; and the guarantee is
  **domain-relative Value** (`Total Trust`*_D* ⟺ `Value`*_D*), not unrestricted Value. It is **not**
  forced to be a better oracle than the human — that limitation is the honest price.

The two positives meet the negative exactly at the ceiling the general theory predicts: you cannot
force an exact early oracle per question, but you can force a faithful statistical accelerator across
questions, and that is the most a modest expert can give. The whole picture connects deference to
**basin-of-attraction / corrigibility** arguments for alignment, the motivating program
(`li-deference.md`).

The reversal of difficulty from DDB and the restoration of the equivalence Weatherson breaks both
trace to one structural fact: an LI expert is a **single belief state**, not a DDB information
*frame* — and LI's two standing scope conditions (bounded LUVs; soft/finite conditioning) are exactly
Weatherson's two infinite-frame breaks.

---

## Where to start

1. **`notes/li-deference.md`** — Abram's human-written motivation (basin-of-attraction arguments for
   alignment; why logical induction; the corrigibility hope and its open problems). Start here for *why*.
2. **`notes/deference-in-logical-induction-v6.md`** — the lead document. Keeps v5's spine and folds in
   the Jun 24–26 work: the second positive construction, the admissibility analysis, domain-relative
   Value, the sharpened negative, an honest Lean status, and a **Vetting Ledger** (Appendix B) listing
   every load-bearing claim with its status. v5 (and v4) are preserved; a v5→v6 map is in the back matter.
3. **`notes/pointwise-tower-and-faithful-acceleration.md`** — the explainer: how the negative and the
   (faithful-acceleration) positive are two faces of the *same object* and meet at one line. Read this
   to see the shape before the details.
4. The two results and the scope fix: **`notes/no-timely-pointwise-tower.md`** *(in `anson-notes/`)* —
   the negative (2a/2b); **`notes/faithful-acceleration.md`** — the positive; and
   **`notes/faithful-acceleration-scope.md`** — the decision note resolving "all sentences" vs.
   "admissible domain" (the admissible-domain version is correct; faithful over-claimed).
5. **`lean/AUDIT.md`** — a statement-level adversarial audit of the five Lean modules: what the kernel
   actually certifies versus what the prose claims. Read this before trusting "kernel-checked."
6. **`transcript.md`** (v5 arc) and **`transcript-v6.md`** (v6 arc) — the substance-only conversations
   behind the notes. Best for the *intuitions* and the turns where things changed.
7. **`anson-notes/`** — the parallel "Trust Between Logical Inductors" project of Anson Berns (with Demski).
8. **`lean/`** — the machine-checked core, if you want to see exactly what is and isn't proved.

---

## Contents

```
README.md            ← you are here
transcript.md        ← the v5-era conversation, substance-only (scrubbed of logistics/infrastructure)
transcript-v6.md     ← the v6-era conversation (faithful-acceleration refinement, the Lean audit, the new results, v6)

notes/
  li-deference.md                              ← MOTIVATION: Abram's human-written framing (basin of attraction / corrigibility)
  deference-in-logical-induction-v6.md         ← LEAD: the tower, the negative result, and two positive constructions; + Vetting Ledger
  pointwise-tower-and-faithful-acceleration.md ← EXPLAINER: the negative & the positive as two faces of one object
  faithful-acceleration.md                     ← POSITIVE: forced gated Value when the AI predicts the human's future credences
  faithful-acceleration-scope.md               ← SCOPE NOTE: "all sentences" vs "admissible domain" — which is right, and why
  deference-in-logical-induction-v5.md         ← prior lead (the spine v6 inherits; the timely-fragment forcing story)
  deference-in-logical-induction-v4.md         ← earlier lead (the anchor v5 was built on; "expert-primary" rewrite)
  deference-in-logical-induction-v3.md         ← earlier rewrite (future-self-primary)
  deference-in-logical-induction-v2.md         ← earlier long draft (full LI-theorem statements in §0.3)
  deference-in-logical-induction-v1.md         ← first draft
  deference-in-logical-induction-check.py      ← sympy sanity-checks (exact rationals)

lean/                 ← kernel-checked: Lean 4.27.0 + Mathlib, all sorry-free, all results audited to the 3 standard axioms
  LeanDeference.lean         ← the tower / Value ⟺ Mart core (§1–§3)
  SelfReferentialTarget.lean ← the self-referential-settlement-target obstruction (§4)
  FrozenDeliberation.lean    ← the complexity-gap hinge + the timely-fragment forcing suite (§5.1–§5.8)
  FaithfulAcceleration.lean  ← the faithful-acceleration trader core (the positive)
  TowerAndAcceleration.lean  ← the tower⇒tracking reduction + the two-faces (½-defect) witness
  AUDIT.md                   ← statement-level audit: what these five modules really certify vs. what they don't
  lakefile.toml  lake-manifest.json  lean-toolchain   ← build config (depends on Mathlib; pins v4.27.0)

anson-notes/          ← the "Trust Between Logical Inductors" project (Anson Berns, with Demski)
  trust-between-inductors-summary-v2.md  ← consolidated technical synthesis (dead vs. live approaches)
  self-referential-settlement-target.md  ← the obstruction note (the dead-ended "§2.2" idea, fully argued)
  no-timely-pointwise-tower.md           ← NEGATIVE: why the timely pointwise tower Mart(H→A) can't be forced (2a/2b)
  frozen-deliberation-deference-v6.md    ← the frozen / sealed-sibling deference construction
  INDEX.md                               ← navigational index over the source conversations
  email-thread-note-dump.md              ← June 2026 email thread that shared/discussed the bundle (transcribed, scrubbed)
  email-thread-timely-tower-theorem.jpeg ← the rendered-LaTeX "no timely tower on the diagonal" theorem, as sent in the thread
  trust-between-inductors-chats/         ← 11 raw exported conversations (the derivations behind the summary)

references/           ← THIRD-PARTY source papers (see note below), full originals
  deference-done-better/
    Deference Done Better.md          ← DDB (transcription)
    DORDDBv1.pdf                      ← DDB (original PDF)
  deference-and-infinite-frames/
    Deference and Infinite Frames.md  ← Weatherson (transcription)
    Weatherson--Deference and Infinite Frames.pdf
  logical-induction/                  ← Garrabrant et al., arXiv:1609.03543 (LaTeX source, compilable)
    main.tex  main.bbl  miri-tech-article.cls  miritools.sty  arxiv-1609.03543.tar.gz
```

The `notes/` material (other than v4, which was machine-written and is kept as the anchor), the
`lean/` development, the two `transcript*.md` files, and this README are the original work in this
bundle. The v-numbered notes supersede one another in order; **v6 is current**, the earlier ones are
kept for provenance and for exposition some carry. The `anson-notes/` are a parallel collaboration
(Anson Berns, with Demski) that v5/v6 integrate.

---

## What is and isn't established

`lean/AUDIT.md` is the honest, statement-level account; the short version:

- **proved (kernel-checked).** All five `lean/` modules are Lean 4.27.0 + Mathlib, `sorry`-free, every
  result auditing to `[propext, Classical.choice, Quot.sound]` (the three standard Mathlib axioms,
  nothing else). What this certifies is the **deference *algebra* and its valid composition** — the
  bookkeeping that the (named, trusted) LI theorems compose into the tower, `Value ⟺ Mart`, the
  self-referential-target obstruction, the timely-fragment forcing, the faithful-acceleration trader
  arithmetic, and the tower⇒tracking reduction + the two-faces ½-defect witness — with no sign error,
  no telescoping sum that fails, no limit that doesn't follow.
- **what the kernel does *not* prove.** It does **not** prove the *forcing* — the genuine
  logical-induction layer (the criterion, `loe`, `expprovind`, Expectation Unbiasedness From Feedback,
  Non-Dogmatism, per-member convergence) enters as **named hypotheses**: we trust the LI paper, we do
  not re-prove it, and the market/trader is itself unmodeled. As the audit puts it, the standing risk of
  the named-hypothesis discipline is a theorem **engineered to typecheck** that tests something *beside*
  the claim it is named for; v6 §7 and the audit flag where the formalization sits closest to that line.
- **sketched / prose.** The trader constructions and the soft-witness continuum lift, at the LI paper's
  level of rigor; and the sharp "squeeze" from soft Total Trust up to the exact tower equality.
- **interpretation.** The alignment / corrigibility framing.

**A correction worth noting**, because it is the kind of thing this bundle is meant to surface: the
positive note `faithful-acceleration.md` originally claimed the result over *all* sentences;
`faithful-acceleration-scope.md` shows that over-claims — calibration provably fails on the
quote-referencing diagonal — so the correct statement is over an **admissible domain**, and the
guarantee is **domain-relative Value**. v6 carries the corrected version. Treat the **Vetting Ledger**
in v6 (Appendix B) as the working checklist of what still needs careful vetting.

---

## Building the Lean (optional)

The `lean/` files were checked against **Lean 4.27.0 + a matching Mathlib**. To reproduce, drop the
`lean/` files into a fresh Lake project and build (it will fetch Mathlib per `lakefile.toml` /
`lake-manifest.json`; fetch the prebuilt oleans first if you want to avoid a from-scratch Mathlib
build). The build artifacts and the Mathlib checkout are deliberately **not** shipped here (size).
Each file ends with `#print axioms …` lines, so a green build re-prints the axiom audit.

---

## A note on `references/`

These are **third-party papers**, included as a convenience so the notes are self-contained:

- **K. Dorst, B. Levinstein, B. Salow, B. Husic, B. Fitelson**, "Deference Done Better,"
  *Philosophical Perspectives* 35 (2021). The `.md` is a transcription.
- **B. Weatherson**, "Deference and Infinite Frames," *Australasian Journal of Logic* (2025). Transcription.
- **S. Garrabrant et al.**, "Logical Induction" (2016), **arXiv:1609.03543**. LaTeX source.

Both original PDFs and the LI LaTeX source (compilable: `.tex` + `.bbl` + `.cls` + `.sty`, plus the
arXiv e-print tarball) are included for completeness. Each markdown transcription carries its own
transcriber's notes. Please **cite and rely on the published originals**; the transcriptions are a
convenience, not a substitute.

A related paper discussed in the conversations — **D. A. Herrmann, A. Chari, I. Qian, S. Sharvesh &
B. A. Levinstein, "A Decision-Theoretic Approach for Managing Misalignment"** — is referenced but not
reproduced here; see the published version.
```
