# The Horty check

`PRIORITIES.md` item 77 names a prior-art check as part of its deliverable, points at
Horty's priority orderings, and predicts they are not enough. `PRIOR_ART.md` §7 records
the same thing as "an open question and a good literature target". This settles it, and
one of the five findings comes out **against** the shape the dispatch predicted.

## 0. What was read

`AGENTS.md` standard 7 forbids a remembered label. So, precisely:

| source | status |
| --- | --- |
| **Horty, *Reasons as Defaults*, Draft #2, 16 August 2006** (79 pp.) | **READ** — the maintainer supplied it mid-round. This is the **paper**, the precursor to the 2012 book, and it carries the formal apparatus in full: Definitions 1–7, fixed- and variable-priority default theories, and **threshold default theories**, which is what the book develops into "exclusionary default logic". |
| Modgil & Prakken, *The ASPIC+ framework for structured argumentation: a tutorial* (2014) | **READ** — PDF, author's site |
| *Defeasible Reasoning*, Stanford Encyclopedia of Philosophy | **READ** |
| Horty, *Reasons as Defaults*, **OUP 2012** (the book) | **NOT read** — still unreachable. Every finding below is checked against the 2006 paper; where the book may have moved, that is flagged. |
| Pollock, *Defeasible Reasoning*, 1987 | **NOT read.** `PRIOR_ART.md` §2 records it as "verified 2026-09-01" against a URL on `umiacs.umd.edu`; **that URL did not resolve during this round**. Horty attributes the undercutting distinction to Pollock 1970 and 1995, not 1987, in this paper. *(Annotation, 2026-09-05: the address redirects to `horty.umiacs.io`, which serves the PDF; `PRIOR_ART.md` now carries the resolving address and the DOI.)* |

**This section replaces an earlier one written before the paper arrived**, which
recorded the primary text as unreachable and marked three findings *unverified*. They
are now verified against Horty's own text, and **two of them are sharpened rather than
merely confirmed** — see Findings 1 and 2. Nothing had to be withdrawn.

### The apparatus, quoted

Horty's four definitions, which every finding below turns on (§2.2, pp. 11–16):

    Triggered_{W,D,<}(S)  = {δ ∈ D : W ∪ Conclusion(S) ⊢ Premise(δ)}
    Conflicted_{W,D,<}(S) = {δ ∈ D : W ∪ Conclusion(S) ⊢ ¬Conclusion(δ)}
    Defeated_{W,D,<}(S)   = {δ ∈ D : ∃ δ' ∈ Triggered(S) with δ < δ'
                                     and Conclusion(δ') ⊢ ¬Conclusion(δ)}
    Binding_{W,D,<}(S)    = Triggered(S) \ (Conflicted(S) ∪ Defeated(S))

A scenario is **stable** when `S = Binding(S)`. Reasons are "identified with the
premises of triggered defaults" (p. 12).

## Finding 1 — Expressibility: can a priority ordering express `dispose`?

**Verdict: no, and for a deeper reason than the item states.**

Item 77 says "a priority ordering says which reason wins, not what licenses the loser
to stop being owed." That is right, but it concedes too much: it presupposes that in
Horty's framework something *is* owed, and that the ordering merely fails to license
the loser's release. Neither is so.

Horty's apparatus computes, from a fixed default theory and a priority ordering, a
**proper scenario** — a rationally acceptable subset of defaults to reason from — and
the conclusions it supports. A default that loses on priority is simply **not in the
selected set**. There is no object in the theory that records that it was ever a
candidate, no quantity attached to it, and nothing that a later stage must discharge.

Mapping the round's three kinds onto that apparatus:

| round's kind | image in Horty |
| --- | --- |
| `answer` | **none.** Horty has conclusions being *drawn*, not obligations being *discharged*. Drawing a default's conclusion is not paying anything. |
| `dispose` | **partial.** A default losing on priority, or being excluded, is the closest thing — but it leaves no successor and no residue. |
| `settle` | **partial.** A change in the facts changes which defaults are triggered, which is settlement lowering demand. |

So the honest statement is not "Horty has defeat but no licence to stop owing". It is:

> **Horty's theory is a theory of what to conclude, not of what is owed.** There is no
> account, so there is nothing for a disposal to move, and the question "what licenses
> the loser to stop being owed" does not arise inside it.

**Verified, and the earlier hedge discharged.** `Defeated_{W,D,<}(S)` is a function of
the scenario, so a default defeated in one scenario may be binding in another; and
Horty exhibits the reactivation directly. In the Drug #3 example (§3.2, p. 38) a new
default forces the undercutter below threshold, and the originally undercut default
"can now **emerge from below threshold** to support the conclusion that the object is
red."

So a defeated default is reactivable — but **by recomputation, not by anyone's licensed
act**, and nothing is owed on its account in the interim. That is the disanalogy with
`dispose`, stated exactly.

## Finding 2 — The direction of the gap

**Verdict: the prediction is right about *which* of D1–D3 have images and wrong about
*why*.**

The dispatch predicted: grounds (D1) yes, successor (D2) no, separation (D3) no,
"because the ordering is exogenous and unauthored."

| clause | image in Horty | |
| --- | --- | --- |
| **D1 grounded** | **yes.** The winning higher-priority default is the ground of the loser's defeat, and in **variable priority default logic** the priority itself is established by higher-order defaults, so the ground is in the record. | prediction correct |
| **D2 routed** | **no.** No successor, no inherited load, nothing carried forward. | prediction correct |
| **D3 separated** | **no.** | prediction correct, reason wrong |

The reason D3 has no image is **not** that the ordering is exogenous — and the paper
lets this be said exactly, because it contains **both** cases.

- **Fixed priority theories** `⟨W, D, <⟩` (§2.1): here the prediction is right. Horty
  says he considers "the special case in which all priority relations among defaults
  are fixed in advance, so that there is no need to consider either the source of these
  priority relations or the way in which they are established."
- **Variable priority theories** `⟨W, D⟩` (§3.1): here it is wrong. The ordering is
  *derived from the scenario itself*, `δ <_S δ'` iff `W ∪ Conclusion(S) ⊢ d ≺ d'`, and
  a scenario is proper for `⟨W, D⟩` exactly when it is proper for `⟨W, D, <_S⟩`
  (Definition 6). Priorities are established by the very reasoning they guide.

So the prediction's reason holds for the theory Horty starts with and fails for the one
he builds. **What is missing throughout is authorship, not endogeneity.**

And the paper makes that sharp, because Horty *does* model authority — twice. He names
it as a source of priority (§2.1: "orders from the Colonel override orders from the
Major"), and in the Nixon example the advice of a church elder and a party official is
"encoded by supplementing the set `D` with the new defaults `δ₃` and `δ₄`."

> **An authority enters Horty's framework as the content of a default, never as a
> participant who holds standing.** There is no resolver, no opener, nobody for a
> separation condition to quantify over. D3 asks a question about *who*, and the
> ontology has no `who`.

That is why the gap is not repairable by making priorities more dynamic: Horty already
did that, and it does not produce a participant.

*(The prediction is, however, exactly right about canonical ASPIC+ — see Finding 5.)*

## Finding 3 — Undercutting: is exclusion answerable? **(the crux)**

**Verdict: yes, exclusion is challengeable in-system — and Horty says so in as many
words. So an exclusionary reason is *not* a settlement fact, and the theory does not
have one summand where the round has two.**

The dispatch set this up as the crux: *if an exclusionary reason is unchallengeable, it
is a settlement fact in the round's typing, not a disposal.* **The antecedent fails**,
and this is now checked against the primary text rather than inferred from SEP.

**The mechanism.** Horty rejects treating undercutting as primitive — "the standard
practice is to postulate undercutting defeat as a separate, and primitive, form of
defeat … this practice is followed, most notably, by Pollock" — and analyses it instead
"simply as a special case of priority adjustment". A threshold value `τ` is posited, and
triggering is revised (Definition 7, §3.2) to

    Triggered_{W,D,<}(S) = {δ ∈ D : τ < δ and W ∪ Conclusion(S) ⊢ Premise(δ)}

so "a default is then undercut when our reasoning leads to the conclusion that its
priority falls below threshold." An undercut default "cannot itself be triggered, and
therefore, **provides no reason of its own**".

**Exclusion is itself attackable.** Three separate confirmations in the text:

1. §3.2, p. 37: "ordinary defeaters and undercutters can themselves be defeated or
   undercut, both defeaters and undercutters of defeaters and undercutters can likewise
   be defeated or undercut, and so on."
2. The Drug #3 example is exactly an **undercutter undercutter**: `δ₅ = D3 → d₄ ≺ t`
   forces the undercutting default below threshold.
3. Footnote 16, p. 39, on the practical side: *"just as in the epistemic case, where
   undercutters can be undercut, **exclusionary reasons can themselves be excluded**:
   perhaps Colin has promised his mistress to disregard any promises made to his wife."*

Horty goes further and **rejects the stratified reading** the dispatch's worry depends
on: he disagrees with "the suggestion … that reasons form a kind of hierarchy, so that,
just as undercutters are 'second-order' reasons, undercutter undercutters are
'third-order' reasons, and so on … His entire life, and the reasons governing it, could
be a tangled mess, but the theory would apply all the same."

**So there is no level the system cannot challenge**, which is precisely the property
the round's `settle` has and `dispose` lacks.

**One qualification, and it is Horty's own.** The *threshold defaults* `δ*_X` are the
exception: the construction requires that they "must lie above threshold; **they cannot
be undercut**", though they *can* be defeated — which is how ordinary defaults get
undercut at all. So the apparatus does contain one unchallengeable layer. But it is
bookkeeping — the grounding that stops an infinite regress of "is this default above
threshold?" — not a normative object, and nothing is owed on its account either. It is
not a `settle` in the round's sense; it is closer to the round's `Settled` being
monotone by construction.

**This is a positive result for the round's two-summand structure.** The worry that the
prior art collapses `dispose` and `settle` into one does not obtain. In the round's
typing an exclusionary reason is a **`dispose` without D2**: grounded, in-system,
challengeable, and moving nothing.

## Finding 4 — What survives as new, and what becomes a dependency

**New.** Phrased so a reader of the books can check it:

> `Triggered`, `Conflicted`, `Defeated` and `Binding` are each a function of
> `⟨W, D, <⟩` and the scenario `S` alone, and a proper scenario is a fixed point of
> `Binding`. In the variable-priority case `<_S` is itself derived from `S`. **Nothing
> in the apparatus is a function of the history of defeats.** Delete every record of
> which defaults lost, recompute, and the answer is unchanged. The same holds of
> ASPIC+ extensions.
>
> The round's defeat theory adds exactly that dependence. A disposed issue leaves a
> named successor carrying its load; `Live`, `Routes`, and the conservation law all
> read it; and the trace's future is not recoverable from its current outstanding set
> alone. Deleting the record of a defeat changes the theorems.

**Said fairly, this is a difference of subject, not a defect in Horty.** His is a
*static* theory — one default theory, compute its proper scenarios — and it is not
trying to model a process over positions. That is exactly why it has no ledger, and it
is the same observation as Finding 1 from the other side: a theory of what to conclude
does not need to remember what it stopped concluding.

That is the account, and it is what neither framework has. The three clauses D1–D3 are
the terms on which a defeat is allowed to create such a successor, and none of them has
an antecedent in either book because neither book has anything for them to constrain.

**Dependency, not resemblance.** `PRIOR_ART.md` §2 already says of Pollock "What we
take: the undercut/rebut split." That is right and should be strengthened in its
wording: the round's `answer`/`dispose` distinction **is** Pollock's rebut/undercut
distinction, transposed from a belief's warrant to a debt's warrant. `answer` rebuts
the challenge-warrant; `dispose` undercuts it. This is a conceptual dependency in the
strong sense — the round did not arrive at two kinds independently — and the
`SUPERSESSION`-style honesty the repository applies elsewhere applies here.

For Horty, the entry should change from "open question" to: **his machinery cannot
express `MayDispose`, because it has no account for a licence to operate on; and his
exclusion mechanism is challengeable in-system, so it is closer to `dispose` than to
`settle`.**

## Finding 5 — ASPIC+ in one section

Read from the Modgil–Prakken tutorial directly.

- **Attack types.** Undermining (attacks premises), rebutting (attacks a conclusion
  with a contrary), undercutting (attacks the inference rule). The three-way split is
  finer than the round's two, and the round's `answer`/`dispose` cuts across it:
  `answer` is rebutting, `dispose` is undercutting, and undermining has no image
  because a disposal attacks the *warrant of the challenge*, not the challenge's
  premises.
- **Does defeat have a successor?** **No.** A defeated argument is excluded from the
  extension; the framework retains no residual trace and no successor. There *is*
  **reinstatement** — an argument defeated at one level may be reinstated if all its
  attackers are themselves defeated — but reinstatement is automatic and structural,
  computed by the semantics, not a licensed act by a participant with a recorded
  ground. It is the opposite of a transfer: nothing moved, so nothing had to come back.
- **Is the attack relation authored?** **No, and here the dispatch's prediction is
  exactly right.** The preference ordering is exogenous in canonical ASPIC+, supplied
  externally rather than derived from arguments. Making preferences themselves argument
  conclusions is possible in principle and is explicitly non-standard. So ASPIC+ has
  neither D2 nor D3, and unlike Horty it does not even have the endogeneity that would
  make the *reason* for lacking D3 interesting.

Prakken 2018 is already cited in `PRIOR_ART.md` for the statics and is not re-derived
here.

## Consequences for the ledger

1. `PRIOR_ART.md` §2's Horty entry and §7's dependency note get the verdict, replacing
   "open question".
2. Pollock's entry is strengthened from "what we take" to a stated conceptual
   dependency of the two kinds.
3. **`PRIOR_ART.md` §2's Pollock URL is dead** and its "*Citation verified 2026-09-01*"
   mark now over-claims — the link does not resolve today. Recorded per standard 7,
   with the verification date left standing as a fact about that date and the link
   marked unreachable.
4. Item 77's prior-art deliverable is **discharged for the theory, not for the book.**
   Every finding is now checked against Horty's own 2006 text, which contains the whole
   apparatus the question was about. What remains unread is the **2012 book**, whose
   contribution over the paper is the development of §3.2's threshold theories into
   "exclusionary default logic" plus the Dancy material. A reader wanting to cite the
   *book* still owes that check; a reader wanting to know whether the machinery can
   express `MayDispose` has the answer.

## Reservation

None new. The dispatch offered one — *whether the round's `settle` and Horty's
exclusionary reasons are the same object* — conditional on the Horty check producing
it. **It did not.** Finding 3 answers the question rather than raising it: exclusionary
reasons are challengeable, `settle` is not, so they are different objects and there is
nothing to reserve. The related settlement-independence reservation from PR79 stays in
the queue on its own terms.
