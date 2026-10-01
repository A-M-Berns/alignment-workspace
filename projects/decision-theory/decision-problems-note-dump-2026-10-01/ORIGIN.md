# Origin — the decision-problems working notes, 2026-10-01

**Status: `agent-consolidated`.** Ordinary content — editable and
reviewable, not machine-protected. The norm is that it is not tweaked. Edit it
when there is a reason, state the reason in the commit, and record substantive
edits in `DECISIONS.md`. Rewriting it to fit new work is not a reason.

## What it is

`decision-problems-v2.md`: working notes toward a formal core for decision
problems. They cover event spaces with designated meets and worlds as two-valued
probabilities (§0), subjective states in Jeffrey–Bolker–Joyce format (§1),
decision procedures, concrete and abstract decision problems, calibration and
the fixed-point problem (§§2–5), comparisons of procedures with worked examples
(§§6–7), and transpositions of the CDT+SIA and EDT+SSA ratifiability theorems to
trees (§8), followed by open questions and two change logs.

The notes are AI-drafted; the generating model was not recorded. They were
reviewed section by section by a maintainer — **the author** below — with Tim
Parker, and the change logs record which revisions came from that review. Claims the
drafter could verify are labelled Theorem/Proposition/Lemma with proofs or
sketches, and the rest Conjecture or Question, as the document's opening
paragraph says. No human has checked every proof.

`../../deference/corrigibility-note-dump-2026-10-01/value-change-as-epistemic-update.md`
§5.1 and Appendix A cite it.

## As received

| | |
|---|---|
| received | 2026-10-01 |
| archive sha256 | n/a — taken from the author's working files, never an archive |
| tree sha256 at intake | `c632a27fa4d860c053bdd2648763d7dec322a9bad5c2dddbcb58d5d7914fcfd5` |
| files at intake | 1 |

## Intake deltas

- **Naming.** The fifteen review credits in the change logs that named the
  author now read *the author*; the one shared credit reads "the author and Tim
  Parker". Tim Parker's own credits are unchanged. Nothing else was edited.

## Vetting status

Working notes, not a statement of record. Nothing in this tree is registered in
this repository's claims sense.

## What cites it

`../../deference/corrigibility-note-dump-2026-10-01/`, at intake.

## Checking this receipt

The tree hash is sha256 over LF-joined lines `<sha256(file)>␣␣<relative path>`,
sorted by path, excluding **this file**. Recompute it that way and you learn
whether the tree has moved since it arrived. This is a receipt, not a gate; the
protection that remains is that this path is specification layer in
`tests/path_gate.py`.
