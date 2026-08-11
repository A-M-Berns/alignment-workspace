# Corrigibility paper ledger

**Canonical for human-readable research status on this line.** Where this document
and `CORRIGIBILITY_ROADMAP.md` disagree about whether something has been
established, this document wins. Where this document and `../CLAIMS.md` disagree
about what has been established *inside this repository*, the registry wins.

## The one-line status

**Nothing on the deference line is `workspace-established`.** `../CLAIMS.md` does
not yet exist, and `lean/Workspace/Deference/Basic.lean` holds a namespace
placeholder and no mathematics. Every result below is inherited, and inherited
status is not repository status.

## Vocabulary

`inherited-established` — direct inspection of inherited material shows the result
was established there; carries no implication about the current proof stack.
`workspace-established` — this repository holds a statement of record meeting its
verification requirements. `architected` — precise enough to organize work, not
established. `open` — substantive mathematical uncertainty. `blocked` — waiting on
an upstream theorem, definition, or maintainer choice. `maintainer-decision` —
reserved.

## Evidence caveat for every inherited row

The rows below are attested by the inherited development's **own statement-level
audit**, `../note-dump-2026-06-27/lean/AUDIT.md`, which classified each theorem by
proof kind and hypothesis provenance. That audit is read as evidence; its Lean was
**not** rebuilt in this round, and the inherited tree carries its own toolchain and
lakefile rather than this repository's. A row saying `inherited-established` means
*the audit attests it*, not *this repository has rechecked it*. Confirming those
rows against the source is filed as `PRIORITIES.md` item 14.

## Movement I — faithful acceleration (`H → A`)

| result | inherited status | kind | what carries it |
|---|---|---|---|
| `value_iff_totalTrust` (finite-exact) | `inherited-established` | proved outright | `witness_identity`, the two-option identity; algebra alone |
| `value_iff_totalTrust_asymptotic` | `inherited-established` | proved, both arrows | linearity; the audit records "neither hypothesis is the conclusion" |
| `decomposition` | `inherited-established` | proved outright | pure linearity, no frame hypothesis |
| `softmax_lower_bound` | `inherited-established` | proved outright | genuine `exp` analysis; was a hypothesis, became a theorem |
| tower ⟹ Value, asymptotic and finite | `inherited-established` **conditionally** | composition | genuinely chains named Logical Induction facts; the facts are named, not derived |
| `soft_total_trust_doublysoft` | `inherited-established` **conditionally** | composition | support hypotheses discharged from the construction; calibration and criterion still named |
| "the criterion *forces* the tower" | **`open`** | — | see below |

The division is the whole story, and it is the inherited audit's own central
finding: **the corpus proves the implications of the deference theory, not its
antecedents.** The algebra composes. The forcing does not follow from anything in
the corpus, because the market and the traders are unmodelled, so every appeal to
"the no-Dutch-book criterion forbids the exploit" is either a named hypothesis or an
arithmetic stub standing in for the arbitrage argument.

The forcing headlines are the sharp case. The audit classifies the cross-process
forcing suite as **squeezes over hypotheses equivalent to their conclusions** — a
theorem whose named hypotheses already contain what its name claims it establishes.
Such a theorem is not false; it is empty, and the difference is invisible to the
kernel. `PRIORITIES.md` items 7–9 are these three findings, filed.

## Movement II — reciprocal delegation (`A → H⁺`)

| result | status |
|---|---|
| cross-agent one-sided Total Trust | `open` — the major theorem |
| finite trust-to-delegation bridge | `open`; first-wave target, item 15 |
| settlement classification | `open`; first-wave target, item 15 |
| contingent WP-D statement | `architected` at best; gated on the settlement decision |

The settlement interpretation is a **`maintainer-decision`**. A contingent theorem
shape may be mathematically ready while interpretive endorsement remains blocked,
and the two readinesses are kept apart.

## Movement III — substitution (`π^SIM`)

`open`; first-wave target, item 17. The distinction between deferring to the actual
principal and predicting it is stated but not formalized. The program is committed
to keeping the thesis compatible with a perfectly predictable principal, so
unpredictability is not available as a cheap separator.

## Movement IV — fully updated deference (`π^{FU,g}`)

`blocked` on WP-C and WP-D, and additionally `blocked` at the level of the finite
model: the shared skeleton does not carry the time-indexed family of `A`-valuations
that `π^{FU,g}` needs, and the round declined to invent one, because inventing it
carelessly is how `π^{FU,g}` silently collapses into `π^SIM`.

## Movement V — certification and densification

Certificate inequality: `open`; first-wave target, item 16, to be derived rather
than imported. Densification: `open`; first-wave target, item 18, deliberately
bounded.

## Movement VI — non-authorship / dose

Inherited material exists at `../dose-response-note-dump-2026-07-02/` and has **not**
been assessed in this round; its status is therefore unrecorded rather than
assigned. Dose does not solve substitution, and the conceptual ordering is principal
individuation → actual-channel responsiveness → bounded shaping.

## Movement VII — preservation

`open`, downstream, untouched.

## The standing gap

One item explains most of the rest. Modelling the market and the traders converts
"criterion ⇒ forcing inequality" from a named hypothesis into a theorem, and it is
the same gap the leverage line and the pinned dependency sit on the other side of.
It is `PRIORITIES.md` item 7 and the most valuable single item in that file.
