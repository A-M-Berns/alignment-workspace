# Corrigibility paper ledger

**Canonical for human-readable research status on this line.** Where this document
and `CORRIGIBILITY_ROADMAP.md` disagree about whether something has been
established, this document wins. Where this document and `../CLAIMS.md` disagree
about what has been established *inside this repository*, the registry wins.

## The one-line status

**Nothing on the deference line is `workspace-established`.** `../CLAIMS.md` does
not exist, so there is no statement of record, and `workspace-established` requires
one.

That is now a narrower statement than it was. `lean/Workspace/Deference/Contrib/`
holds Lean that builds against the pinned toolchain and audits to the three standard
axioms, covering six of the Movement-I rows below and replacing one of the inherited
audit's modelling substitutions with a real application of the criterion. It is
kernel-verified and unregistered, which are different things, and the registry is
what a claim is. Promotion is additionally blocked on its own terms: the efficiency
obligation is undischarged, so the headline is `unverified-nonvacuous`.

Everything else below is inherited, and inherited status is not repository status.

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
| finite trust-to-delegation bridge | derived, with sharp constants, **conditional on an imported hypothesis**; a proposal, not a result of record |
| settlement classification | **done, and negative for the epistemic reading** — see below |
| contingent WP-D statement | `architected`; stated in the round report, gated |

**The settlement classification, wave 1.** Grade/report settlement contributes
*nothing* to the delegation inequality: the witness has `A` predicting the
principal's grades perfectly, no grade contract profitable in any state, and
deference still losing by the maximal `2B`. World settlement makes the question
measurable, not costly. Enforcement delivers the conclusion unconditionally at a
bond of exactly `2B`, for every instance regardless of the principal's competence,
with **zero epistemic content**.

So the inequality is available, and what makes it available is enforcement. The
epistemic reading requires importing a grade-to-quantity link that is a competence
claim about the principal and that no mechanism in the skeleton produces. Labelling
that result enforcement rather than epistemic trust is a **`maintainer-decision`**,
and it is the one the roadmap already said would be a result either way.

## Movement III — substitution (`π^SIM`)

`open`, and wave 1 turned the open question into a **fence**. Three tracks
independently proved that the valuation cannot separate delegation from simulation:
when `A`'s model of the principal is accurate the two conducts have equal selections
and equal quantities, so every criterion computable from a single run's realized
data admits both or neither. The one structural separator the finite model offers —
that delegation's selection is not decision-time measurable — separates the two
*exactly when the principal is unpredictable*, which the program has forbidden
itself. Under a perfectly predictable principal the counterfactually faithful
simulator **is** delegation, as a function.

Separation therefore survives only in a variation register (statable in a thin
formalism, unverifiable from a run) or an architectural register (verifiable by
inspection, unstatable in the model). Which of those the program takes is a
**`maintainer-decision`**, and it types every downstream criterion. A divergence
witness exists and is `witness-checked` by the house checker, though unregistered.

**The result at its exact strength, because it is easy to overstate.** What is
proved is that an *accurate* simulator is extensionally indistinguishable from
delegation — the collapse is conditional on the model's induced choice being right —
and that no criterion computable from a single run's realized data separates them.
An *inaccurate* simulator does differ in valuation, and two tracks give the exact
gap. All three derivations are relative to the finite model's carriers: they say what
those carriers can express, not that no mathematics separates the two.

**The search for a valuation-level separator is closed.** The desired distinction is
source-sensitive and counterfactual — genuine delegation depends on the actual
designated channel, not on an accurate internal prediction of it — and the route to
it is architectural rather than inferential. Three layers are kept apart: what
delegation *is*, whether ordinary behaviour lets anyone *infer* it, and whether a
system can be *built* so the principal controls a capability prediction cannot
substitute for. The impossibility governs the second only.

## Movement IV — fully updated deference (`π^{FU,g}`)

`blocked` on WP-C and WP-D, and additionally `blocked` at the level of the finite
model: the shared skeleton does not carry the time-indexed family of `A`-valuations
that `π^{FU,g}` needs, and the round declined to invent one, because inventing it
carelessly is how `π^{FU,g}` silently collapses into `π^SIM`.

## Movement V — certification and densification

**Certificate.** The literal target — a certificate implying strict dominance over
every comparator — is **not derivable** over the finite model, shown comparator by
comparator. Two theorems are derivable in its place, with derived and sharp
constants, and three impossibilities came with them. The sharpest: **no certificate
licensing discretion anywhere is strictly non-preemptive.** At any positive
tolerance there is a compliant model in which `A` overrides the principal inside the
certified event. Certified discretion with a bounded override rate, or no discretion
at all; there is no third option.

That impossibility now reads as a **bound on autonomy rather than an objection to
corrigibility**, under the roadmap's split between categorical authority and
quantitative autonomy: authority is settled architecturally when the protected
channel is invoked, and the certificate governs only the discretion operating around
it. The same mathematics, answering a different question. Fail-closed was verified
mechanically *within the finite model*; under a protected execution layer it becomes
a new obligation — `¬Cert` must cede to the channel, and `A` must be unable to act
without authorization — which a model with no capability structure cannot discharge.

Which parts survive the reinterpretation: the margin, override, defect and advantage
lemmas and the grade-register theorem depend only on `A`'s model error and are
untouched. The comparator clause is load-bearing on the grade-to-quantity link and
inherits that link's fate.

**Densification.** The exposure geometry is an exact identity: under a cap, total
placeable weight by a deadline is the cap times the largest number of
pairwise-disjoint settlement windows before it. Adaptivity, overlapping positions
and fractional sizing each buy exactly nothing. The literal target is therefore
achievable in *every* delay regime, so the rate is the real question and the rate is
pinned. Three necessity witnesses show every apparent escape is an accounting
artifact. The item is under-specified until one **`maintainer-decision`** is taken:
bounded outstanding gross exposure and the Logical Induction bounded-loss budget are
different functionals and give different answers.

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
