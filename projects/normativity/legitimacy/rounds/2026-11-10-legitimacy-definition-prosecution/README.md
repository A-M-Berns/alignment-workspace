# Legitimacy: manipulation as inducing or exploiting a mistake

Round `2026-11-10-legitimacy-definition-prosecution`.

**`CURRENT.md` says where the line stands**: what is solid, what was tried and not kept, and
what is in progress, each with the file or declaration that carries it. `VERDICTS.md` holds
the verdict each pass recorded. `withdrawn/WITHDRAWN.md` gives five withdrawn claims with an
instance each. `earlier-attempts/` holds the statements of the account that later passes
replaced. The report is
`prompts/2026-11-10-legitimacy-definition-prosecution/REPORT.md`.

The account formalises Robert Noggle's Mistake Account (*Manipulation: Its Nature,
Mechanisms, and Moral Status*, OUP 2025; "The Mistake Account of Manipulation", *Journal of
Practical Ethics* 14(1), 2026, doi:10.3998/jpe.9951). That a faculty is for something and
manipulation distorts her away from it is Sam Eisenstat's idea. Related work on the same
problem: Nora Ammann, *The Value Change Problem*
(<https://www.alignmentforum.org/s/3QXNgNKXoLrdXJwWE>). All names are provisional.

## Run

    python3 run.py          # every pass: banks, statements, the account's checks, the withdrawn claims' instances
    python3 run.py --json   # the same as data

About two minutes. Exit nonzero when a bank parses to nothing, when a computed verdict
diverges from its bank without a line in that pass's `DIVERGENCES.md`, when a listed
divergence does not occur, when a status or a count in a document is not the one computed,
or when `withdrawn/WITHDRAWN.md` does not carry a computed number. Python 3.9+ standard
library; exact rationals; no network. `tests/run.py` hands over to `run.py` so the
repository-level runner finds it. The Lean:
`~/.claude/scripts/safe-lake.sh build Workspace.Deference.Contrib.ScoringTheorem` from
`lean/` (it imports the other two files); in CI, the `lean` job.
