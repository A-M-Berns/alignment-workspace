# faf-cleanroom addendum — the `corr-value-change` package (2026-10-07)

One further work package of the clean-room formalization run published as
[`faf-cleanroom-2026-10-02`](../faf-cleanroom-2026-10-02/README.md): a Lean 4
formalization, over [Formalized Agent Foundations](https://github.com/A-M-Berns/Formalized-Agent-Foundations)
(FAF), of the note
[value-change-as-epistemic-update](../corrigibility-note-dump-2026-10-01/value-change-as-epistemic-update.md)
— value change as conditioning on a finer algebra, Good's theorem for value
change, reflection conditional on legitimacy, trust without the outcome events,
the finite Jeffrey–Bolker and superconditioning pictures, and the causal version
— written and adversarially audited on 2026-10-07 under the run's standards
([STANDARDS](../faf-cleanroom-2026-10-02/STANDARDS.md)). It is published beside
the bundle rather than inside it so that the bundle's intake receipt stays what
it was. Status and provenance are in [`ORIGIN.md`](ORIGIN.md).

**Register.** Everything here is AI-generated (Claude Fable 5.1 agents) and has
not been vetted by the author. Kernel-checked means the proof is a proof of the
statement as written; whether the statement is the claim is what the package's
audits judge, and they are AI judgments too. The sixteen findings the package
recorded about the note
([`corr-value-change-findings.md`](packages/corr-value-change/corr-value-change-findings.md))
were folded into the note's 2026-10-07 revision, which is the version published
beside this tree.

## This tree is not built by this repository's CI

Like the bundle, this package is pinned to FAF `159ec3f` and builds inside the
bundle's Lake project, which takes hours; the repository's `lean` job builds
`lean/**` only. Moving its results into `lean/` is future work.

## Verify it yourself

From a checkout of this repository, with [elan](https://github.com/leanprover/elan)
installed (the bundle pins the toolchain, Lean v4.31.0):

```bash
B=projects/deference/faf-cleanroom-2026-10-02
A=projects/deference/faf-cleanroom-2026-10-07-corr-value-change
cp -r $A/Cleanroom/Corrigibility/CorrValueChange.lean $A/Cleanroom/Corrigibility/CorrValueChange $B/Cleanroom/Corrigibility/
cd $B
lake exe cache get                                            # Mathlib oleans
lake build Cleanroom.Corrigibility.CorrValueChange            # the package root and its imports
python3 scripts/audit.py --no-replay Cleanroom.Corrigibility.CorrValueChange
```

The package imports eight modules of the bundle's `Cleanroom/Found/LitDdbFrames/`
(its Total Trust definition) and nothing else outside itself; those eight modules
were byte-identical in the run's working tree and in the bundle on 2026-10-07.
The root `Cleanroom.lean` of the bundle does not import this package, so a plain
`lake build` there does not build it.

## Mechanical state at intake (2026-10-07)

- **Build:** 22 modules (21 under `Cleanroom/Corrigibility/CorrValueChange/` and
  the root `CorrValueChange.lean`), all built; no `sorry` anywhere; the package's
  open list (`corr-value-change-open.txt`) is empty.
- **Gate** (`scripts/wp-audit`, which runs `scripts/audit.py --no-replay`, after
  repair round 4): 1,361 declarations; axioms used: `propext`, `Classical.choice`,
  `Quot.sound`; 0 `sorry`, 0 `native_decide`, lint clean. The run's root open
  list had every entry twice (it is the union of the package lists since the
  run's consolidation), which made the gate's open-list check fail on
  infrastructure until the duplicates were collapsed; the one-line fix is in the
  working tree's `scripts/wp-audit`, not in the bundle's copy.
- **Kernel replay** (`leanchecker`): not run for this package.
- **Audits:** four rounds, two lenses each (statement fidelity; attempted
  breakage), with a repair after each round; the final round is published here
  with its probe files, the earlier rounds are summarized in the report. Every
  core target (T1–T13) has Lean at grade (a); the stretch targets S1–S6 are
  done; of the extension tier (the infinite translation of §5.3–5.4 and
  Appendix A) E4, the Radon–Nikodym form, is done in measure-space form and
  E1–E3 and E5 were not attempted, with no `sorry`-ed statement left behind
  (the report says why).
- **Clean room:** the package's agents did not open the earlier independent
  run's files or transcripts; each report and audit carries its declaration.

## What was not shown

- That the statements are the claims of the note: that is the audits' judgment,
  not the kernel's.
- The infinite translation (E1–E3, E5): the ultrafilter construction over an
  abstract Boolean algebra, the Stone space, and Bolker's uniqueness. The note's
  §5.3–5.4 and Appendix A are not formalized.
- An independent kernel replay.
- Vetting by the author of any result.

## Layout

| path | contents |
|---|---|
| `Cleanroom/Corrigibility/CorrValueChange.lean`, `Cleanroom/Corrigibility/CorrValueChange/` | the Lean, namespace `Cleanroom.Corrigibility.CorrValueChange`, one file per target or theme (`Model`, `Table`, `TwoStep`, `Product`, `Examples14`, `Epist`, `Update`, `Good`, `Fine`, `Variants`, `Teacher`, `CondLegit`, `AltForm`, `Modest`, `TotalTrustTwo`, `JeffreyBolker`, `Prop58`, `Supercond`, `Savage`, `Epistemicize`, `RadonNikodym`) |
| `packages/corr-value-change/` | `corr-value-change-report.md` (the formalizer's report, the repair rounds and the final gate), `-findings.md` (the sixteen findings about the note), `-ledger.md` (one row per headline), `-open.txt` (empty), the round-4 audits (`-audit-r4-fidelity.md`, `-audit-r4-adversarial.md`) and their probe files (`audit-r4-probes/`) |
| `ORIGIN.md` | the intake receipt |

Links from the package documents to `STANDARDS` go to the bundle's copy; links
to the note go to the corrigibility note dump beside this tree; names of files
that are not published (the mandate, the earlier audit rounds, the run's audit
prompt) appear as code spans.
