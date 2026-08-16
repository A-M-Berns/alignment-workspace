# Contributing

## For readers

If you have just arrived, five things.

**1. Verify before you trust.** Seven gates run in CI and five of them run
locally, with the commands in the next section. Every claim in this repository is either
machine-checked by them or **explicitly labelled otherwise** — the frozen
consolidation, for instance, separates machine-checked results from hand-derived
ones from transcribed ones from a reading audit, and says which is which per
claim.

**2. Read provenance before you cite.** Every artifact declares two things: its
**generator** — a maintainer, a maintainer's round, or an external contributor —
and its **review status**, `maintainer-reviewed` or `ci-only`. `ci-only` means
exactly what it says: the gates passed and no maintainer has read it. It is
allowed here, because this is a working repository and a label that lies is worse
than an honest one, but it is never hidden. See `AGENTS.md`.

**3. Verification lives here; interpretation lives in the wiki.** Repository
deliverables state claims, hypotheses, checks, and local consequences plainly.
The maintainer-written GitHub wiki is the human register. Contributors do not
read it as instructions or edit it; interpretation they believe is warranted
goes in the pull-request description for maintainer consideration. Its source is
`wiki/` here, and contributors do not touch that directory unless a
`PRIORITIES.md` item directs it.

**4. The two hard rules** are that consolidated work is not tweaked and that
names are the author's to set.

**5. Disagreement is welcome, and it has a format.** Not an opinion: a
counterexample, a failing test, or a precise objection filed as an issue against
a named ledger item. That is not gatekeeping — it is the same standard the
repository's own results are held to, and a good counterexample is worth more
here than agreement.

---

**Quality here is enforced by machine-checkable gates, not by trust.** You do not
need to be known to anyone to contribute. Your pull request either passes the
seven gates or it does not, and the gates are the same ones the author's own work
passes.

## Run everything locally first

```sh
python3 tests/run.py                              # python: every project's tests
python3 tests/name_lint.py                        # python: no personal names in prose
python3 -m checkers.run --self-test               # checkers: the harness's own tests
python3 -m checkers.run                           # checkers: every registered claim
python3 tests/contrib_hygiene.py                  # checkers: contributed checkers
python3 -m checkers.wiki_links                    # checkers: wiki links resolve and are pinned
python3 tests/path_gate.py                        # path-gate: which layer your files are in
python3 tests/workflow_scope.py                   # python: CI write scope is enumerated
python3 tests/conservativity.py                   # conservativity: no new axioms
cd lean && lake exe cache get && lake build       # lean: sorry-free
python3 tests/audit_axioms.py                     # lean: axiom audit
cd projects/normativity/consolidation-aug9 && python3 tests/run.py   # consolidation-verification
```

The comment names the CI job each command belongs to. Two gates have no local
form: `dco` reads your commits' sign-offs, and the attribution check reads the
pull-request body, which does not exist until you open one.

If these pass locally on a clean checkout, the rest is the pull request itself.

## What you can contribute

Every file in this repository belongs to exactly one layer, and which one decides
what you may do to it.

**The proof layer is open to you.** Lean proofs of statements of record and new
lemmas in contribution namespaces; witnesses and domain parameters; documentation
of contributed results.

**The specification layer is not.** Definitions and statements of record, the
checker harness, CI, toolchain pins, the axiom allowance, budgets, and the
governance documents. A `path-gate` CI job fails any non-maintainer pull request
that touches one. There is no trusted-contributor tier that bypasses it — if your
work genuinely needs a specification change, open an issue proposing it.

Identity is never a factor in a proof-layer verdict. Anonymous and pseudonymous
contributions are fine.

### Minimal glossing

Repository contributions explain what was tested and what the result means for
the claim under test. Roadmaps, narrative framing, and broader philosophical
positioning belong in the maintainer-written wiki. Padding remains a sufficient
reason to reject a contribution even when its local gloss is accurate.

### Nothing enters the record unasked

**Every registered claim answers a filed `PRIORITIES.md` item.** Propose new
items as issues; filing is not a contributor's. An unsolicited-but-correct
contribution is not merged into the record — but the maintainer may file a
matching item and then accept it, so good work is not wasted, only sequenced.

### Research output is not registered state

A completed round supplies candidate evidence. A result becomes consumable as
current workspace state only through:

`round artifact → statement of record → registered claim/status → current workspace state`

The presence of a proof, witness, experiment, criticism, conjecture, or report in
a completed round does not itself promote a claim. Changes to registered claims,
project status, vocabulary, priorities, or theorem-facing interfaces update the
corresponding structured state in the same pull request. Check it with
`python3 -m checkers.workspace_state --check`; inspect it with
`python3 -m checkers.workspace_state --json`.

The query reports modern registered claims and inherited foundation claim sets
separately. A foundation keeps its own ledger and status vocabulary; its results
are not silently translated into the modern registry's epistemic classes.

### Submission format, by claim class

| you are claiming | you submit | what adjudicates it |
|---|---|---|
| **a Lean theorem** | the proof, in a contribution namespace, plus a term inhabiting its full hypothesis package | the Lean kernel, the axiom audit, and the nonvacuity check |
| **an existential, counterexample, sharpness or necessity witness** | **data** — the instance — plus the house checker id and the property parameters | `checkers/witness.py`, which you did not write and cannot change |
| **something the house checkers cannot express** | your own checker in `checkers/contrib/`, plus the claim | your checker — and the claim is capped at `contributor-checked` |
| **a finite universal claim** | **domain parameters** only | `checkers/enumeration.py`, which generates the domain itself |
| **anything over an infinite domain, or sampled** | the work, registered as `test-supported` or `conjectured` | nothing — it is **not citable as proven**, and its natural fate is a Lean port |

### You may ship a checker with a new claim

Put it in `checkers/contrib/` — that directory is open, and the path gate will
let you add to it without a maintainer. Your claim is then registered
**`contributor-checked`**: the certificate ran and passed, and the logic that
judged it has not been read by a maintainer yet. The registry derives that
ceiling from the invocation path, so there is nothing to remember and nothing to
declare.

**This is an invitation, not a consolation.** The class is honest rather than
punitive, and there are two ways out of it: a maintainer reads your checker, it
becomes house, and every claim it certified upgrades in one batch; or the claim
is ported to Lean and the checker is mooted.

**Prefer Lean where you can.** On the Lean side the kernel is the judge, so you
can write arbitrarily much new content with no maintainer in the loop and no
class penalty at all. The Python harness stays small on purpose.

What you may **not** do is modify a house checker in `checkers/`. That is
retroactive — every claim it has already certified would silently re-inherit your
change — which is why one is gated and the other is merely labelled.

**You never ship the verifier for a claim of record.** A test file of your own
may support exploration, but the thing that certifies a registered claim is
always a house checker. If a contributor supplied the enumeration, the
contributor would be certifying the claim — the enumeration *is* the proof.

A theorem also does not enter the record without an **inhabitation witness**: a
concrete instance satisfying all its hypotheses. A theorem whose hypotheses
nothing satisfies is not false, it is empty, and that difference is invisible to
the kernel.

## What a contribution must contain

**A theorem** ships as four things:

1. a **statement** — in a `THEOREMS.md` or a docstring — that a reader can
   evaluate without reading the implementation;
2. an **implementation**, in exact rationals (`fractions.Fraction`; floats only
   in clearly-marked exploration code, and no result may depend on one);
3. a **test** that recomputes the claim exactly; and
4. a **necessity witness for each hypothesis** where feasible — a displayed
   instance showing that dropping the hypothesis breaks the result.

Where a necessity witness is not feasible, say so in the statement. An
unexamined hypothesis is a gap, and naming it is not a failure.

**Lean** ships building and auditing clean: no `sorry`, `#print axioms` at the
end of the file, and every result auditing to
`[propext, Classical.choice, Quot.sound]` and nothing else. **External theory
enters as named hypotheses of the statement that uses it — never as an `axiom`
declaration.** An `axiom` standing in for a citation is the specific failure the
gate exists to catch.

**A witness** ships as the exact instance and the check that verifies it. "There
is a counterexample" is not a witness; the counterexample is.

## Where to find work

`PRIORITIES.md`. It is the source of truth and it tags difficulty: **[entry]**
items need no new mathematics, **[substantial]** items are scoped results,
**[open]** items may be impossible. GitHub issues mirror that file, not the
reverse — if the two disagree, the file is right.

## The two hard rules

*(Stated above for readers; here is what they mean for a pull request.)*

**1. Consolidated trees are not yours to edit.** The consolidations and
received bundles inside each research line are `agent-consolidated`: ordinary
content, but the norm is that they are not tweaked, and the `path-gate` job puts
them out of a contributor's reach. Cite them by path and by claim identifier.
Work that needs a consolidated result to say something different is work that
supersedes it with a later tree — not work that rewrites it.

**2. Contributors do not coin permanent names.** Naming is the author's.
If your work needs a name for something new, use an obviously provisional one,
mark it, and list it in the pull request's "new names introduced" field. This is
not bureaucracy — a name that ships is very hard to change later, and the
program's vocabulary has already been through one painful retirement.

## Sign your commits

Every commit carries a Developer Certificate of Origin sign-off:

```sh
git commit -s          # adds the Signed-off-by line
git commit --amend -s  # fixes one you forgot
```

The sign-off asserts the DCO in [`DCO`](DCO) — that you have the right to submit
the work under this repository's licence. CI checks every commit in a pull
request.

**Pseudonymous sign-offs are accepted.** The maintainers know that is a thinner
assertion from a pseudonym than from a known person, and accept it deliberately:
Apache-2.0 §5 is the primary rights mechanism and the DCO is the recorded
assertion on top of it. Identity is not a factor in a proof-layer verdict, and
this does not make it one — the gate checks that an assertion was made, not who
made it.

## Citation integrity

No unverified identifiers. Cite content inline, or cite a claim identifier
against a checksummed frozen tree. **Never a remembered label.** If you cannot
verify a citation against the source it names, state the content directly and say
that the label did not check out — that has caught real errors here, including
labels attributed to sources that do not contain them.

## Prose

`AGENTS.md` has the rule in full; the short form is that every sentence does
work. No restatement, no padding structure, no inflated register, no hedging that
is not a real epistemic state — the epistemic classes are where uncertainty gets
recorded. This is not style policing: padding hides errors in the restatements,
and it inflates the cost of the review this repository runs on. **A pull request
whose content is correct and whose prose is padded can be rejected on that
ground.**

## Review

**A pull request whose required checks all pass merges automatically.** Enable
auto-merge on your pull request and GitHub lands it when the last check goes
green; nobody has to be awake. A red one is not argued with.

That is the architecture's own conclusion rather than a convenience: the gates
decide correctness, and if they do, waiting on a person adds a delay and not a
check. What review still decides is fit, naming, provenance labelling, whether
both documentation registers are present, and whether a result belongs in the
program — and those are judgments about work already merged, raised as issues or
follow-up pull requests like anything else.

Two things make this safe rather than reckless. A non-maintainer pull request
touching a specification path **cannot go green** — the `path-gate` job fails it
— so full green already means the change is confined to the open layer. And
`conservativity` fails anything that adds an axiom, changes specification shape,
or alters the axiom output of an existing declaration.
