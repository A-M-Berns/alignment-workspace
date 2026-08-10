# SI v3 — changelog

Every edit from `SETTLEMENT_INTERFACE.md` (draft 2.1) to
`SETTLEMENT_INTERFACE_v3.md`, keyed to the revision items R1–R8 and to the audit
or review section each implements. Then the R2 citation-verification table, then
the flagged-not-fixed list.

Housing: v3 sits beside draft 2.1 and the audit rather than in
`normative-learner/`, for the reason the audit gives about itself — the tree's
naming gate rejects several words this document needs, including the one it uses
for the logical residue. Nothing in either tree was modified by this revision.

---

## R1 — C1 operationalization
*Implements: audit §1 C1; review pt. 3; audit prediction π3 (PARTIALLY CONFIRMED).*

- **Replaced** the D∞ definition. The interface's logical class is now named
  `Dec(D)`, the **D-decidable fragment**: sentences the declared process
  eventually proves *or* whose negation it eventually proves. The document now
  states explicitly that this is **not** the union of what the process proves,
  and gives the correct relation `Dec(D) = { φ : φ ∈ D_∞ or ¬φ ∈ D_∞ }`.
- **Fixed the erroneous display.** Draft 2.1 wrote a set inequality with `⊊`
  between the interface's D∞ and `D_∞ ∪ ¬D_∞`, which is malformed: the two
  sides are not comparable as written, and the intended content is the
  definition above, not an inclusion.
- **Added** one clause on the Gödel case: for a theory such as Peano arithmetic
  the fragment is a proper subset of the language, since a Gödel sentence lies
  in neither the proven set nor its negation image.
- **Added** the consequence the audit draws: C1 is satisfiable only under a J1
  **declaration discipline** — the declared jurisdiction must lie inside the
  engine's own decidable fragment — and the document now calls that a real
  obligation rather than a formality.
- **Kept verbatim** the ratelessness language and the parenthetical that
  completeness is relative to the declared process. The audit confirms this is
  the clause the audited engine fits best; nothing there needed changing.

## R2 — Citation verification
*Implements: audit §1 C3 citation-integrity flag; audit §6.*

The C3 citation was replaced and **every** other corpus citation in the document
was checked against `consolidation_aug8/` and `normative-learner/`, and every
paper citation against the Logical Induction source. Results in the table below.

Twenty citations were checked. Eight verified cleanly and are now stated as
content. Four verified but were cited defectively — one under a name the corpus
does not use, one located in a different tree, and two against paper labels of
which one does not exist. Six required a correction to the document: one
half-real, one embellished, two claiming corpus antecedents that are not there,
one restated, and one terminology error. Two are not corpus results at all — an
internal decision and an external one-pager not present here.

The general policy applied: where a claim identifier survived verification, its
**content** is now stated in the sentence that cites it, so the document reads
without the other trees open. Where an identifier did not survive, the content
is stated directly and the historical narrative dropped.

**One correction to the audit itself.** The audit reports that "no identifiers
`A0`, `CA-*`, or `MSR-A` occur in `normative-learner/LEDGER.md` or in the
consolidation's markdown." `A0` **does** occur, twice in
`consolidation_aug8/LEDGER.md` (rows for the bare-bridge failure and the
relativized bridge, in the necessity column as "VII A0") and once in
`consolidation_aug8/tests/test_tier_a.py`. The audit's grep appears to have been
too narrow. `CA-*` and `MSR-A` are genuinely absent. So the C3 citation was
half-real, not wholly unresolvable — which is a better outcome than the audit
reported, and is recorded here so the audit can be corrected in turn.

## R3 — T1 non-vacuity
*Implements: audit §1 T1 (the sharpest finding), audit §5 π2; review pt. 4.*

- **(a) Added T1.a.** The clause now states in its own text that it admits
  vacuous satisfaction: a declared `ε_t ≡ 1` never breaches and never certifies,
  because at that tolerance the robust interval is the whole unit interval and no
  merits certificate clears — the same degeneration the empty-book recovery
  result displays. Added the **non-vacuity definition**: a declared tolerance is
  *working* iff the induced ε-robust interval can strictly separate for some
  nonempty book, and *working* is a property of the declaration together with the
  displayed book, checkable per date.
- **(a, continued) Marked the owed definition.** The exact finite-time defect
  functional is left as a definition the document owes, per instruction — with
  the sentence the instruction asks for: without a declared normalization,
  "ε ≡ 1 bounds the defect" is **not meaningful**, since there is no scale on
  which 1 is large and an engine could satisfy any schedule by rescaling its
  measure.
- **(b) Added T1.b, the two routes.** Route 1, an engine-certified computable
  modulus, is stated as **open in both directions** with the audit's warning
  carried: the adjacent impossibility is not this statement. The warning is
  sharpened — see "additions beyond the brief" below. Route 2, the book-declared
  working tolerance under T2, is labelled **the operating mode**.
- **(c) Kept the candidate weakening** as a stated, non-adopted alternative,
  with its downstream cost spelled out: the merits certificate becomes *a
  posteriori*, and both the recomputation discipline and the merits-iff-leverage
  biconditional would need restating. Their content is now given inline.

**Addition beyond the brief, flagged.** The audit says the Sawin-et-al.
incompatibility is "adjacent" and must not be cited as settling the modulus
question. v3 says *why*, in one clause: that result and the paper's own
three-way impossibility both turn on Gaifman inductivity, a desideratum the
algorithm already fails, whereas the modulus question involves no Gaifman
condition at all. This is a sharpening of the audit's warning, not a new claim,
but it is an addition and is marked as one.

## R4 — J2 conditional status
*Implements: audit §1 J2; review pt. 1.*

- **Restated J2's inhabitation** for deductive engines as an explicit
  conditional inside §2: consistency of the declared theory ⇒ write-once;
  inconsistency yields a double pin on one report variable, which §7 classifies
  as a jurisdiction violation and routes to the breach stack. The document now
  says plainly that consistency is a hypothesis and is not provable in the
  theory itself.
- **Added the principle to §7**, as instructed and as a standing rule rather
  than a remark about this case: **breach handling is cost allocation, never
  satisfaction.** A clause is not satisfied by the constitution knowing what to
  do when it is violated. The paragraph also preserves the audit's genuinely
  positive observation — that the one case where the pen can violate write-once
  is precisely the case the breach stack was built for — while denying that this
  amounts to inhabitation.

## R5 — B3 restated to the pair
*Implements: audit §0 (the central mapping decision) and §4.*

- **Replaced the B3 statement.** B3 now quantifies over the **pair** ⟨D, P⟩,
  with a two-row table assigning the deductive process to the pen and clock and
  the market to the purse, tolerance and certificate type, and with the audit's
  argument for why the alternatives fail.
- **SI⁻ as instructed:** `{ J1, J3, C1, C2, C3, P2, P3, P4, T2,
  F2-via-precommitment, §9(i) }`, C3 marked vacuous on the logical channel, F2
  by the precommitted witness only. **J2 and P1 are pulled out of the set** and
  presented as named conditionals — on consistency and on Δ₁ respectively.
  *Note a difference from the audit:* the audit's §2 lists J2 and `P1*` **inside**
  SI⁻ with qualifying bullets. The instruction's arrangement is followed here;
  it is the cleaner statement, since a conditional inhabitation is not an
  inhabitation. Recorded so the two documents can be reconciled.
- **Added the Δ table** with the four classifications: Δ₁ open sub-problem
  (stable core floor under region contraction); Δ₂ modification, negligible
  (proof-carrying process); Δ₃ modification-or-weakening (tolerance); Δ₄
  reserved (funding-responsive deduction).
- **Named the consistency hypothesis explicitly** in both §2 and B3.
- **Added the Δ₄ two-versions sentence:** *acceleration* (fixed process, budget
  buys progress by wall-clock) versus *attention* (budget selects what the
  process works on, making the stream endogenous), with the observation that
  only the second makes the plausible-world set funder-dependent, and the
  statement that the interface does not choose between them.

## R6 — Witness table update
*Implements: audit §2, §4.*

- **Row 1 changed from positioning hypothesis to AUDITED**, with the SI⁻ summary
  inline in its cells and the section pointer to the restated B3 below the table.
- **The banner was rewritten** to except row 1 and to keep every other row
  unchanged as a positioning hypothesis pending literature and witness audit.
- **The P2 cell notes "inhabited literally by the Budgeter construction"**, and
  a paragraph below the table gives the reason at the level of the construction:
  the budgeter zeroes a strategy once its value reaches −b in **some**
  propositionally-consistent world consistent with the deductive state, which is
  a worldwise floor and strictly more than an expected-value constraint, and the
  trading firm bounds aggregate exposure through a summable budget schedule.
  Presented as the audit does, as the strongest single line of evidence that the
  interface carves at a real joint.

## R7 — Consistency sweep

- **§0 auditability paragraph.** Draft 2.1 asserted flatly that "the pen's
  conformance to its declared tolerance is auditable (a Farkas check)". After
  R3 that is only true *given a fixed measure of incoherence*, which the document
  does not yet fix. The sentence now says so and points at §5.
- **§0 clause-level legend.** Rechecked against the revised clauses; unchanged.
  P1 remains [M] — the relative reading changes what is checked, not who imposes
  it.
- **§6 F2.** Draft 2.1's "Two named witnesses satisfy it" implied both are
  available to every engine. The audit shows one candidate engine has only the
  precommitted route, because a global asymptotic guarantee over a whole price
  sequence issues no per-request certificate for an anytime-valid route to
  instantiate. The clause now says the condition is neutrality, the two are
  instances, availability is engine-relative, and draft 2.1 read wrongly.
- **§7 breach list.** The tolerance-violation entry now carries "once §5's
  functional is fixed", so the list does not promise a check the document cannot
  yet define.
- **§8 terminology.** "Proof kernel" → "proof checker" throughout, with a note
  on why: the corpus reserves that word for its own formal object and states
  that the Lean proof checker is not a name of it.
- **§8 residue paragraph.** "The logical debt at the checker kernel" → "at the
  checker", consistently with the above.
- **§11.** Rechecked against the revised clauses. The conjunct list is unchanged
  and remains true of them; the compiler-contract block is added after it (R8).
- **§12.** Compressed from a fourteen-row provenance table to a paragraph, per
  the register instruction.
- **§13.** Rewritten to match the revised open set: Δ₁ and Δ₃(a) promoted to
  named items, the owed functional added, the compiler-contract confirmation
  added, and the §10 literature audit narrowed to rows 2–8.
- **Housing notes** trimmed to one sentence each, per the register instruction.

## R8 — P1 adoption and the mechanism-side hypotheses

**The P1 restatement had not carried.** The brief states that the relative-core
restatement is an adopted author decision "already applied to the input draft".
It is not: `SETTLEMENT_INTERFACE.md` as supplied is byte-unchanged in P1 from
draft 2.1, still reading "The engine certifies a fixed core coefficient θ > 0 (or
a floor θ_min for a varying core)" with no relative/ambient language anywhere in
the file. **Verification failed, and the restatement is applied here.** If a
revised draft exists elsewhere, this v3 was built from the file supplied and the
two should be reconciled before anything downstream is keyed to either.

- **Applied the relative reading** to P1: the core condition is read against the
  post-settlement feasible simplex, with the necessity witness glossed in the
  clause — under the ambient reading the clause is *unsatisfiable* for every
  positive coefficient from the first exact pin, since a pin is an equality and
  the endorsed region falls into a hyperplane while the homothet keeps the
  simplex's dimension. The gloss notes the non-degenerate confirmation (a
  three-world instance whose post-pin region is still a segment), so the failure
  cannot be read as an artifact of a collapsed region.
- **Added the per-date consequence:** containment is linear in the reference at
  fixed coefficient, so satisfiability at a date is a linear program, with
  clipping where the admissible region is non-empty and **quarantine of
  operative force** where it is empty. Immediately followed by the limit: no
  per-date check bounds an infimum over time, so persistence is the open residue
  and is Δ₁.
- **Added the compiler contract** as a named block in §11, *flagged for the
  author's confirmation rather than asserted*, listing the four mechanism-side
  hypotheses: publication before demand; coherent extension to fresh sentences;
  a summable drift schedule; and the solver budget. The solver budget carries an
  explicit "this is not T1" paragraph — T1 bounds the distance of the engine's
  **prices** from coherence, the solver budget bounds the distance of the
  compiler's **chosen quote** from the constrained optimum, neither implies the
  other, and the two documents each carry only one of them.
- **Stated the resulting shape** of the composite: the engine satisfies the
  interface, the compiler satisfies its contract, and then the bound holds.

---

## R2 citation-verification table

Every corpus or paper citation appearing in draft 2.1, with what verification
found and what v3 does. "Tree" is `consolidation_aug8` (C) or
`normative-learner` (N); "paper" is the Logical Induction source.

| # | draft 2.1 citation | where | verification | resolution in v3 |
|---|---|---|---|---|
| 1 | §1 "the reports-only jurisdiction" | decision D-I.1 | internal decision, not a corpus result | kept; decision detail moved to the §12 note |
| 2 | §1 "the recycling species already refuted in the corpus" | C | **verified, name supplied**: the persistent-false-bound result — a false exposed bound survives repeated tests under external replenishment when only current locks are tracked (REFUTED, witness displayed) — repaired by the capped-net-outflow convergence result | content stated inline; no identifier needed |
| 3 | §2 J2 "the per-provenance subsidy and fencing machinery" | C | **verified**: the subsidy key is the provenance class the token gate already represents, with a misdeclared-provenance objection and a public ancestry check | content stated inline |
| 4 | §2 J3 migration cells | N | **verified**: administrative continuity (only a declared grant is permitted between certified migrations) and the migration-transport requirement of exact outstanding meaning on the common carrier or an explicit legacy disposition | content stated inline |
| 5 | §3 C3 "the A0 witness and its CA/MSR-A repair" | C, N | **split**. `A0` **exists** — the Tier-A witness carried by the bare-bridge failure result, contra the audit. `CA-*` and `MSR-A` do **not** exist in either tree. The repair is the **operational adequacy** hypothesis of the relativized bridge: capped stake, token envelope, work-conserving service, and a latency/capacity comparison. Downstream analogue: the service-inadequacy witness | historical narrative dropped; the failure, the repair and the downstream witness are stated as content |
| 6 | §4 P2 "bounded aggregate trader budgets" | paper | **verified as content**; **label wrong**. The audit cites `defprop:Budgeter`; no such label exists. The construction is a `defprop` environment titled Budgeter in the subsection "Constructing Budgeter"; the only label in it is on the displayed condition | content stated inline in §10; no label cited |
| 7 | §4 P3 "finite FIFO world slots with canonical least-block scheduling" | C | **split**. "fill freed world slots FIFO" is verbatim in the uniform policy's transition cycle. "least-block scheduling" is **not** in either tree; the actual rules are *least unresolved objection with exposed inconsistency first* and *date-major admission*. The cap is the token-envelope queue result; finite overtaking is a hypothesis of the uniform-mechanism construction | corrected to the actual selection rules |
| 8 | §6 F3 "the insider pattern of the corpus's conduct machinery, extended verbatim" | C, N | **not verified**. No insider, blackout, or disgorgement content exists in either tree. The corpus's conduct family's displayed member is the cross-component transfer objection: a public fence declaration, a typed transfer, upheld on crossing, vacuous with no fence | rewritten: F3 is **a new conduct type**, built in that family's shape; "extended verbatim" removed |
| 9 | §6 F4 "the common-source objection surface" | C, N | **not verified** as an existing surface; the per-provenance keying it would feed **is** verified | rewritten: the objection type is new, the provenance keying is reused |
| 10 | §8 "record-twin ... results" | C | **verified under another name**: the glossary maps Public-Twin Extensionality to *record extensionality*, and seam/world/procedure twins to *record-seam-equivalent traces* | renamed to record-extensionality |
| 11 | §8 "gauge results" | C | **verified**: the stock and flow gauge results, i.e. the declared conjugacies, with the flow one holding only after balances, recipients, transfers and payment outcomes join the preserved signature | kept, content stated |
| 12 | §8 "the deference results" | neither tree | **verified but located elsewhere**: they live in the Logical Induction formalization tree, not in the corpus this document otherwise cites | kept, with a locational note added |
| 13 | §8 "the corpus's meta-challenge machinery already bottoms out at a mechanical proof checker" | C | **partially verified**. "Meta-challenge" is not a corpus term; **finite meta-depth** is part of the syntactic layer, and judges are finite record checkers | restated as "judges bottom out in finite record checkers over a finite meta-depth" |
| 14 | §8 "a fixed proof kernel" | C | **terminology error**: the glossary reserves that word for the mechanism object and states explicitly that the Lean proof checker is *not* a name of it | changed to "proof checker" throughout, with the reason noted |
| 15 | §5 (via audit) recomputation discipline; merits-iff-leverage | N | **verified**: the unsupported-merits rejection, and the merits biconditional over the feasible set built from the simplex, the pinned record and the endorsements as one-sided constraints | content stated inline in T1.c |
| 16 | §5 (via audit) empty-book degeneration | N | **verified**: the empty-book recovery result — no endorsements and no settled premise bearing on the target | content stated inline in T1.a |
| 17 | §3 C2 clock and admission results | N | **verified, four of four**: clock-derived refusal accounting; no-free-silence; necessity of admission; finite-overtaking fairness | content stated inline |
| 18 | §10 the Sawin-et-al. incompatibility | paper | **verified**, and found to be **two distinct results** in one passage: the paper's own three-way impossibility (computable + coherent + Gaifman), and the cited four-way one (computable + non-dogmatic + Gaifman + very weak coherence) | both stated; the shared reliance on Gaifman inductivity is what v3 uses to explain why neither settles the modulus question |
| 19 | audit's paper labels, checked as a set | paper | **eight of nine exist**: the deductive-process, market-process, world, belief-state, pricing and exploitation definitions, and the limit-coherence and main construction theorems. The ninth, `defprop:Budgeter`, does **not** | v3 cites no paper labels; content only |
| 20 | §11 "stated in full in E3" | neither tree | **unverifiable here**: E3 is an external one-pager not present | retained as a forward reference, unchanged |

Supporting content claims spot-checked against the paper while verifying #19:
the belief-state definition does require finite support ("0 for all but finitely
many φ"), which is what P3's row 1 leans on; and the deductive-process
definition is a computable **nested** sequence with `D_∞` its union, which is
what J2's write-once argument and R1's correction both lean on. Both check out.

---

## Flagged, not fixed

Items that looked like they needed redesign. None was touched.

1. **F3 and F4 are new clauses, and the draft's framing hid that.** "Extended
   verbatim" made them read as free imports of existing machinery. They are not:
   the corpus has no insider or common-source surface. As new conduct types they
   owe what every objection type owes — declared judge footprints, a disposition,
   a necessity witness — and none of that is in the interface. **Design question:
   do F3/F4 stay, and if so what discharges their obligations?**

2. **The compiler contract's home.** Four mechanism-side hypotheses are named in
   §11 under a candidate name. Whether they belong in this document at all, or in
   E3, or in a third document about the compiler, is an architecture decision.
   The name itself is also unconfirmed.

3. **Adopting a defect functional.** T1 marks the definition as owed. A candidate
   now exists from the ε-robust docket work, with a normalization that is forced
   by the dual rather than stipulated, which is exactly the property T1 argues is
   needed. Adopting it into the interface is a design decision and was not taken
   here. **Until it is taken, T1's non-vacuity condition is well-posed but its
   conformance test is not.**

4. **C3's general form now exists and is not in the clause.** C3 says the
   adequacy inequality is "stated per instance and checkable". A general form is
   now available — a per-query inequality (admission plus upstream horizon plus
   service fits the deadline) together with a release-aware window inequality —
   and folding it into the clause would be new content, so it was not folded in.

5. **SI⁻ membership differs between the audit and this revision.** The audit puts
   J2 and a starred P1 inside SI⁻; this revision pulls them out as named
   conditionals. Both are defensible; they should not both stand. Flagged for
   reconciliation. One substantive consequence was caught while making the
   change and is fixed rather than flagged: with J2 inside the set, consistency
   of the declared theory rides along as a qualifying bullet, but with J2 pulled
   out, the Δ-sufficiency statement must name consistency explicitly or lose it.
   v3's sufficiency clause names it.

6. **The audit's C3 citation-integrity flag is partly incorrect** (item 5 of the
   table). The audit should be corrected, or a note appended to it, so the
   erroneous "occurs in neither tree" claim does not propagate.

7. **§0's Farkas claim may not survive the adopted functional.** The sentence is
   now conditioned on a functional being fixed, but whether a Farkas check is the
   right conformance test for whichever functional is adopted is open. The
   candidate in item 3 does admit a normalized Farkas-style certificate, which is
   encouraging but not a decision.

8. **Register discrepancy in the brief.** The register paragraph says this
   remains an internal architecting document; the deliverables list calls it "the
   external document". Resolved in favour of the register paragraph — v3 is
   marked internal draft 3 — since the register is the more specific instruction
   and the consolidation freeze is named as the precondition for an external
   version. Flagged in case the deliverables line was the intended one.

9. **§9 untouched, as instructed** — including its framing sentence about
   LI-like constructions being the believed inhabitants, which the audit's
   §9(ii)–(iii) findings arguably bear on. Reserved, so not examined.
