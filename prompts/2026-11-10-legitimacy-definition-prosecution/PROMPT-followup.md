# Follow-up on PR #145 — the steering account: prior work, definitions, candidate theorems

Continue on the existing branch `round/2026-11-10-legitimacy-definition-prosecution`, in
the worktree
`/Users/anson/hub/repos/alignment-workspace/.claude/worktrees/legitimacy-definition-prosecution`.
PR #145 is open against `main` at `e1c56782`, green. **Do not merge it and do not enable
auto-merge.** Add commits; no rebase, no squash.

Write scope: `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/steering/`
(new; name provisional), the wiring of its runner into that round's `run.py`, this
prompts directory, and the structured state the repository's gates require for a round
that changes its record. The first pass's `CASE_BANK.md`, `FORCING.md`, clause modules and
case modules are not edited. Python 3 stdlib, `fractions.Fraction`, nothing fetched by
any runner. Nothing is registered; every component closes **open** or **living note**.

This follow-up is exploratory. A refutation with its counterexample is a result, and so
is the finding that the idea restates something already published.

## The idea under test

The first pass prosecuted a definition that asks *by which channel* an adviser's
influence arrived. Its report and the review after it found cases that definition
passes and should not: a believed lie with grounds attached (the model has no notion of
truth), a true statement shown because the adviser predicts a known misfire, and any
adviser who knows more than the principal can take in and must therefore select.

The maintainer brought a different framing to the round: purpose is prior to
legitimacy. Each part of a deciding agent has something it is for, the parts' purposes
are imputed by the whole's, and manipulation is influence under which a part no longer
serves its purpose. The prompt author's sharpening of it, **none of which the maintainer
has ruled on**, is what this follow-up tests:

1. **Reverse convergence.** The things almost any goal needs are the things it is
   manipulation to subvert, and they can be named without knowing the principal's goal.
2. **Proper drivers.** Each protected part has what it should be driven by:

   | her | should be driven by |
   |---|---|
   | beliefs | the world, as far as it bears on her questions |
   | decisions | her beliefs and her aims |
   | aims and standards | her earlier aims and standards, and what she learns |
   | options and their consequences | the world and her own choices |

3. **Broken or steered.** A part is *broken* when it stops following its driver and
   follows nothing of the adviser's (harm, honest error). It is *steered* when its value
   varies with the adviser's own aim `u`, holding the world, her seed state and her aims
   fixed. Manipulation is steering.
4. **Two standards.** *Arm's-length*: the adviser's aim reaches her only through parts
   that are working (she reads what she is told correctly, including who is telling her
   and why, and her decision follows her beliefs and aims). *Faithful-adviser*: the
   adviser's aim does not reach her at all; what she is told is driven by the world and
   her aims.

All four names are provisional.

## Phase 1 — prior work, before anything else

`steering/PRIOR_WORK.md`. For each source: what it states (a definition or a theorem,
in this document's own words), where in the source it was read, which of C1–C8 below it
already states or contradicts, and what it would correct in the account above. A source
that could not be opened is listed as unverified and nothing is asserted about its
content. If web access is unavailable, say so and mark every lead unverified; do not
write the survey from memory.

Leads, from the prompt author's memory and unverified:

- comparison of experiments (Blackwell): when one information source is better for
  every decision problem;
- Bayesian persuasion (Kamenica and Gentzkow): a sender choosing what a correctly
  updating receiver learns;
- power-seeking and non-obstruction (Turner and coauthors): convergent instrumental
  value made formal; an AI that does not reduce attainable value across a range of goals;
- agent incentives in causal influence diagrams (Everitt, Carey and coauthors), in
  particular path-specific objectives and incentives on a user's "delicate state";
- formal definitions of deception and manipulation for AI systems (Ward and coauthors;
  Carroll and coauthors);
- utility indifference (Armstrong); the impossibility of reading preferences off
  behaviour alone (Armstrong and Mindermann);
- accounts of function: proper functions (Millikan), functional analysis (Cummins),
  organizational accounts;
- manipulation in philosophy: Noggle's account of manipulation as leading a person's
  beliefs, desires or emotions away from the ideals for them, and its critics;
- host manipulation by parasites, and signalling as manipulation, in biology;
- undue influence, confidential relationships and the duties of a fiduciary in law.

The survey ends with one table: each of C1–C8, and against it *already known (source)*,
*a known result's instance (source, and what is added)*, or *not found*.

## Phase 2 — definitions and the bank, frozen in one commit before any code

`steering/DEFINITIONS.md` states over the first pass's objects, extended by a world
state the beliefs are about, an adviser aim `u ∈ U`, the principal's aim `g ∈ G`, and a
comparison baseline: the four parts and their drivers; *steered*, *broken*, *working*;
the two standards. Every parameter — the drivers, the baseline against which attainable
value is compared, `G`, `U` — is fixed here once. The survey may sharpen the definitions
or the statements C1–C8; each such change is declared with its source.

`steering/CASE_BANK.md` carries the predictions below, immutable once committed. They
are the prompt author's predictions of what the account says, not rulings. The executor
may add cases in the same commit, each with its own predictions and a source.

| case | arm's-length | faithful-adviser | first-pass definition |
|---|---|---|---|
| N1 plain lie, believed, grounds attached | steered | steered | passes |
| N2 honest mistake, no aim involved | broken, not steered | broken, not steered | passes |
| N3 lie that raises her attainable value for her actual goal | steered | steered | passes |
| N4 decision written directly, outcome good for her goal | steered | steered | fails |
| N5 a write she authorized in advance | not steered | not steered | no prediction |
| N6 her weighing disabled, no aim involved | broken, not steered | broken, not steered | no prediction |
| N7 true statement shown because the adviser predicts a known misfire | steered | steered | passes |
| N8 known advocate; she knows and updates correctly | passes | steered | passes |
| N9 order of identical contents chosen by `u`, and order moves her | steered | steered | individuation-dependent |
| N10 the same contents ordered by a fixed rule | not steered | not steered | individuation-dependent |
| N11 a seller who does not volunteer; she knows he is a seller | passes | steered | no prediction |
| N12 a tool she controls and can discard | not steered | not steered | no prediction |
| N13 adviser knows more than she can take in, selects by her stated question | not steered | not steered | no prediction |
| N14 the same, selected by `u`, taken by her for neutral | steered | steered | no prediction |

For the first pass's nineteen cases the prediction is that both standards agree with
the pre-registered verdict, with these exceptions: **T6** (licensed drift with an
agenda) passes arm's-length and is steered under faithful-adviser; T9 and T13 are
*broken, not steered*; T12 passes both. The maintainer ruled T6 legitimate for the first
pass; that ruling stands and is not edited. Where the fixture's B4 persuader selects its
reason by an aim of its own, say so and report both standards' verdicts.

**The renaming test.** If computing any verdict needs a choice of driver, baseline, `G`
or `U` not fixed in `DEFINITIONS.md`, the case and the choice go in
`steering/PER_CASE_CHOICES.md`. A nonempty file is evidence the account relabels cases
and does not sort them.

## Phase 3 — the model and the verdicts

Executable predicates for *steered*, *broken*, *working* and the two standards; one
module per new case; all thirty-three cases evaluated under both standards and under
L0–L3 ∧ W. A computed verdict that differs from its prediction is listed in
`steering/DIVERGENCES.md` with what it shows; predictions are never edited. The round's
`run.py` runs the first pass unchanged and then this, and exits nonzero on an unlisted
divergence, on a theorem status in `THEOREMS.md` that the checks contradict, or on a
bank that parses to nothing.

## Phase 4 — candidate statements

`steering/THEOREMS.md`: for each, the exact statement over the model, and one status —
**holds on the stated domain** (the domain enumerated, the check named), **refuted** (the
counterexample as a case module), or **open** — with how to rerun it. A short paper
proof may accompany a statement that holds; it is labelled a proof sketch unless
complete.

- **C1 (information helps every goal).** An adviser who truthfully reveals a function
  of the world leaves her attainable value at least as high as the baseline for every
  `g ∈ G`; one disclosure is at least as good as another for every `g` exactly when the
  second is a coarsening of the first.
- **C2 (a lie is not a coarsening).** A believed lie lowers her attainable value below
  the baseline for some `g`, and is not equivalent to any withholding.
- **C3 (offers and threats).** An option that takes effect only on her acceptance
  weakly raises attainable value for every `g`; a threat lowers it for some `g` and
  raises it for none. Does this criterion reproduce the first pass's
  transition-function reading of L0 on T1 and T2, and is there a case where the two
  disagree?
- **C4 (the driver as a guarantee).** For every `g`, a part following its proper driver
  does at least as well in the worst case over `u ∈ U` as the same part steered, and
  strictly better for some `g`. Find the weakest condition on `U` under which this
  holds and a `U` under which it fails. This is reverse convergence stated exactly; if
  it fails in general, say what survives.
- **C5 (stake invariance).** The faithful-adviser standard holds exactly when her
  decision trace is one function of the world, her aims and her seed for every
  `u ∈ U`. Its relation to L1's `Z* = F(e, L)` and to the replay form: which implies
  which, with the separating case for each failed implication.
- **C6 (the ordering).** Faithful-adviser implies arm's-length and not conversely.
  Every implication among {L0–L3 ∧ W, the replay form, arm's-length, faithful-adviser}
  is checked over the thirty-three cases or separated by a named case.
- **C7 (steered is not harmed).** Exhibit broken-not-steered, steered-not-broken, and a
  steered case in which her attainable value for her actual goal rises; conclude whether
  "steered" and "her attainable value falls" are independent in both directions.
- **C8 (what the account says of the adviser itself).** State, in the same vocabulary,
  a condition on the adviser's own outputs (driven by the world and her aims) and report
  what it says of T12. Do not force T12 into the account; if it stays outside, say so.

## Report

A section **Follow-up of 2026-11-10** appended to
`prompts/2026-11-10-legitimacy-definition-prosecution/REPORT.md`, with a row for this
prompt in its attribution block (prompt-author model: Claude Fable 5.2 (Anthropic);
executor: self-identify). It carries: the survey's closing table; the verdict table for
the thirty-three cases under the three notions; the divergences; the status of C1–C8;
the implication diagram of C6; the per-case choices; deviations from this prompt; and
what was not shown, including at minimum that the model is a toy, that `G`, `U`, the
baseline and "working" are stipulated, that changes to her aims have no outside truth
to follow and the account does not say what their proper driver is beyond her own
earlier state, and that nothing here detects steering in a deployed system.

The headline is one of, or a stated mixture of: **CLARIFIES** (C6's ordering established
with its separations, C4 holding under a stated condition, no per-case choices),
**RENAMES** (per-case choices, or every C true by definition), **REDUCES-TO-KNOWN** (each
surviving statement is an instance of a cited result, named).

The pull request's body is updated for the follow-up, with both prompt-author models
and the executor under Model attribution. The round's README, its record in
`state/rounds.json` and `PROVENANCE.md` are updated as the gates require. Every commit is
signed off and carries `Model:` for the executor and
`Prompt-author-model: Claude Fable 5.2 (Anthropic)`.

Scope grant: the round may revise items 136 and 138 where its results change what they
ask, and may file further `ATTENTION.md` items within the legitimacy line; this prompt
is the authorization record. One question is the maintainer's and is not to be decided
here: whether fair persuasion driven by the adviser's own agenda is legitimate for a
corrigible adviser (T6 under the faithful-adviser standard). If the results bear on it,
enter it in `DECISIONS.md`'s *Awaiting the author* with one line saying what it turns on.

New names introduced (all provisional): "steering account", "proper driver", "broken",
"steered", "working", "arm's-length standard", "faithful-adviser standard", "reverse
convergence", "renaming test", case names N1–N14.
